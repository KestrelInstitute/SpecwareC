
(*** Specs represented as dependent records ***)

Require Import List.
Import ListNotations.
Require Import String.

Add LoadPath "." as Specware.
Require Import Specware.Util.


(* Define the type of fields in one place, so we can change it later *)

Definition Field : Set := string.
Definition Field_dec : forall (f1 f2 : Field), {f1=f2} + {f1<>f2} := string_dec.

(* Type-level versions of bool and unit (needed below) *)
Inductive boolT : Type := | trueT : boolT | falseT : boolT.
Inductive unitT : Type := | ttT : unitT.

Definition boolTT : Type := boolT.
Definition unitTT : Type := unitT.

Lemma neq_trueT_falseT : trueT = falseT -> False.
  discriminate.
Qed.

(* The types bool and unit (in universe Type) are unequal *)
Lemma bool_neq_unit : boolTT = unitTT -> False.
  intro e; apply neq_trueT_falseT.
  transitivity (eq_rect unitTT id (eq_rect boolTT id trueT unitTT e) boolTT (eq_sym e)).
  unfold eq_rect; destruct e; unfold eq_sym; reflexivity.
  transitivity (eq_rect unitTT id (eq_rect boolTT id falseT unitTT e) boolTT (eq_sym e)).
  destruct (eq_rect boolTT id trueT unitTT e); destruct (eq_rect boolTT id falseT unitTT e); reflexivity.
  unfold eq_rect; destruct e; unfold eq_sym; reflexivity.
Qed.


(*** Dependent record types ***)

(* Dependent record types, indexed by their fields *)
Inductive RecType : forall {flds : list Field}, Type :=
| RecType_Nil : RecType (flds:=nil)
| RecType_Cons f {flds} A (rectp: A -> RecType (flds:=flds)) :
    RecType (flds:= f :: flds)
| RecType_ConsAxiom f {flds} (P : Prop) (rectp: P -> RecType (flds:=flds)) :
    RecType (flds:= f :: flds)
.

(* Map a function over the fields of a RecType *)
Fixpoint map_RecType (g : Field -> Field) {flds} (rectp : @RecType flds) :
  @RecType (map g flds) :=
  match rectp in @RecType flds return @RecType (map g flds) with
    | RecType_Nil =>
      RecType_Nil
    | RecType_Cons f _ A rectp' =>
      RecType_Cons (g f) A (fun a => map_RecType g (rectp' a))
    | RecType_ConsAxiom f _ P rectp' =>
      RecType_ConsAxiom (g f) P (fun pf => map_RecType g (rectp' pf))
  end.

(*** Subtypes ***)

(* README: need subtype to be predicative in order to project along it! *)
(*
Inductive subtype : Type -> Type -> Prop :=
| subtype_refl A : subtype A A
| subtype_trans A1 A2 A3 (s1 : subtype A1 A2) (s2: subtype A2 A3) : subtype A1 A3
| subtype_subsume A (P1 P2: A -> Prop) (sub: forall a, P1 a -> P2 a) :
    subtype (sig P1) (sig P2)
| subtype_restrict A (P: A -> Prop) : subtype (sig P) A
| subtype_true A (P: A -> Prop) (truth: forall a, P a) :
    subtype A (sig P)
.
*)


(*** Models, aka records, aka heterogenous lists ***)

Definition Any := { A : Type & A}.
Definition mkAny A a : Any := existT id A a.
Definition dummy : Any := mkAny unit tt.

Definition Model := list (Field * Any).

(* Get just the fields of a model *)
Fixpoint Model_fields (model:Model) : list Field :=
  match model with
    | nil => nil
    | (f,_)::model' => f :: Model_fields model'
  end.

(* Project a field from a Model, returning unit if the field is not
   there; i.e., all models intuitively map unused fields to unit *)
Fixpoint Model_proj (model : Model) f : Any :=
  match model with
    | nil => dummy
    | (f', any) :: model' =>
      if Field_dec f' f then any else Model_proj model' f
  end.

(* Project just the type component from a Model *)
Definition Model_projT (model : Model) f : Type :=
  projT1 (Model_proj model f).

(* Project just the object component from a Model *)
Definition Model_projO (model : Model) f : Model_projT model f :=
  projT2 (Model_proj model f).

(* Projecting a field not in a model always gives the dummy value *)
Lemma Model_proj_not_in model f (not_in: ~In f (Model_fields model)) :
  Model_proj model f = dummy.
  induction model.
  reflexivity.
  unfold Model_proj; fold Model_proj; destruct a; destruct (Field_dec f0 f).
  elimtype False; apply not_in; rewrite e; left; reflexivity.
  apply IHmodel; intro i; apply not_in; right; assumption.
Qed.


(* When a Model is a model of a RecType *)
Inductive IsModelOf_RT (m: Model) : forall {flds}, @RecType flds -> Prop :=
| IsModelOf_RT_Nil : IsModelOf_RT m RecType_Nil
| IsModelOf_RT_Cons f {flds}
                    (rectp : Model_projT m f -> @RecType flds)
                    (model_of : IsModelOf_RT m (rectp (Model_projO m f)))
 : IsModelOf_RT m (RecType_Cons f (Model_projT m f) rectp)
| IsModelOf_RT_ConsAxiom f {flds} (P:Prop) pf (rectp : P -> @RecType flds)
                         (model_of : IsModelOf_RT m (rectp pf))
 : IsModelOf_RT m (RecType_ConsAxiom f P rectp)
.


(*** Removing fields from a model ***)

(* FIXME: this whole section can be rewritten in terms of
   rectrict_model, below (or the section could be removed!) *)

(* Remove a single field *)
Fixpoint Model_remfield f (model:Model) : Model :=
  match model with
    | nil => nil
    | (f',elem) :: model' =>
      if Field_dec f f' then
        Model_remfield f model'
      else
        (f',elem) :: Model_remfield f model'
  end.

(* Model_remfield is correct *)
Lemma Model_fields_Model_remfield f model :
  Model_fields (Model_remfield f model) = remove Field_dec f (Model_fields model).
  induction model.
  reflexivity.
  destruct a; unfold Model_remfield; unfold Model_fields;
  fold Model_fields; fold Model_remfield; unfold remove; fold (remove Field_dec).
  destruct (Field_dec f f0).
  apply IHmodel.
  unfold Model_fields; fold Model_fields; rewrite IHmodel; reflexivity.
Qed.

(* Removing an unequal field does not affect Model_proj *)
Lemma Model_remfield_Model_proj f model f' (neq: f <> f') :
  Model_proj model f' = Model_proj (Model_remfield f model) f'.
  induction model.
  reflexivity.
  unfold Model_remfield; unfold Model_proj; fold Model_proj; fold Model_remfield;
  destruct a; destruct (Field_dec f0 f'); destruct (Field_dec f f0).
  elimtype False; apply neq; transitivity f0; assumption.
  unfold Model_proj; rewrite e; rewrite F_dec_true; reflexivity.
  assumption.
  unfold Model_proj; fold Model_proj; destruct (F_dec_false _ Field_dec _ _ n);
  rewrite e; assumption.
Qed.

(* Remove duplicate fields *)
Fixpoint Model_remdups (model: Model) : Model :=
  match model with
    | nil => nil
    | (f,elem) :: model' =>
      (f,elem) :: (Model_remfield f (Model_remdups model'))
  end.

(* Model_remdups is correct *)
Lemma Model_remdups_nodups model : NoDup (Model_fields (Model_remdups model)).
  induction model.
  apply NoDup_nil.
  destruct a; apply NoDup_cons; fold Model_remdups; fold Model_fields;
  rewrite Model_fields_Model_remfield.
  apply remove_In.
  apply NoDup_remove; assumption.
Qed.

(* Removing duplicate fields does not affect Model_proj *)
Lemma Model_remdups_Model_proj model f :
  Model_proj model f = Model_proj (Model_remdups model) f.
  induction model.
  reflexivity.
  destruct a; unfold Model_remdups; unfold Model_proj;
  fold Model_proj; fold Model_remdups.
  destruct (Field_dec f0 f).
  reflexivity.
  rewrite IHmodel; apply Model_remfield_Model_proj; assumption.
Qed.

(* Removing duplicate fields does not affect IsModelOf *)
Lemma Model_remdups_IsModelOf_RT model flds (rectp: @RecType flds)
      (ismodelof: IsModelOf_RT model rectp) : IsModelOf_RT (Model_remdups model) rectp.
  induction ismodelof.
  apply IsModelOf_RT_Nil.
  revert rectp ismodelof IHismodelof;
  unfold Model_projT; unfold Model_projO; rewrite Model_remdups_Model_proj; intros;
  apply IsModelOf_RT_Cons; assumption.
  apply (IsModelOf_RT_ConsAxiom _ _ _ pf); assumption.
Qed.


(*** Lowering (FIXME: this section is no longer needed) ***)

(* Lower Prop P inside rectp, i.e., augment it to quantify over all
   types / axioms of rectp. Note that lowering P is stronger than
   (forall m, IsModelOf_RT m rectp -> P) since lowering is insensitive
   to duplicate fields *)
Fixpoint RecType_lowerP {flds} (rectp: @RecType flds) (P:Prop) : Prop :=
  match rectp with
    | RecType_Nil => P
    | RecType_Cons f' flds' A' rectp' =>
      forall a, RecType_lowerP (rectp' a) P
    | RecType_ConsAxiom f' flds' P' rectp' =>
      forall pf, RecType_lowerP (rectp' pf) P
  end.

(* Same as above, but in Type instead of Prop *)
Fixpoint RecType_lower {flds} (rectp: @RecType flds) A : Type :=
  match rectp with
    | RecType_Nil => A
    | RecType_Cons f' flds' A' rectp' =>
      forall a, RecType_lower (rectp' a) A
    | RecType_ConsAxiom f' flds' P rectp' =>
      forall pf, RecType_lower (rectp' pf) A
  end.

(*
Lemma lowerP_Cons f A {flds} (rectp: A -> @RecType flds) (P:Prop) :
  RecType_lowerP rectp P -> 
*)

Lemma lowered_in_model {flds} (rectp: @RecType flds) (P:Prop)
      (loweredP: RecType_lowerP rectp P)
      model (ismodel: IsModelOf_RT model rectp) : P.
  induction ismodel.
  apply loweredP.
  apply IHismodel; apply loweredP.
  apply IHismodel; apply loweredP.
Qed.


(*** Properties of models ***)

(* When two models are equivalent on a given set of fields *)
Definition model_equiv_on flds (model1 model2: Model) : Prop :=
  forall f, In f flds -> Model_proj model1 f = Model_proj model2 f.

(* model_equiv_on is symmetric *)
Lemma model_equiv_on_sym flds model1 model2 :
  model_equiv_on flds model1 model2 ->
  model_equiv_on flds model2 model1.
  intros mequiv f i; symmetry; apply mequiv; assumption.
Qed.

(* model_equiv_on satisfies a subset property *)
Lemma model_equiv_on_subset flds flds' model1 model2 :
  incl flds' flds ->
  model_equiv_on flds model1 model2 ->
  model_equiv_on flds' model1 model2.
  intros sub mequiv f i; apply mequiv; apply sub; assumption.
Qed.

(* IsModelOf is preserved when two models agree on all fields in a RecType *)
Lemma IsModelOf_RT_equiv {flds} (rectp: @RecType flds) model1 model2 :
  IsModelOf_RT model1 rectp -> model_equiv_on flds model1 model2 ->
  IsModelOf_RT model2 rectp.
  intro ismodel1; induction ismodel1.
  intros; apply IsModelOf_RT_Nil.
  intro mequiv; revert rectp ismodel1 IHismodel1;
  unfold Model_projT; unfold Model_projO; rewrite (mequiv f);
  intros; [ | left; reflexivity ].
  constructor; apply IHismodel1; intros f0 i; apply mequiv; right; assumption.
  intro mequiv; apply (IsModelOf_RT_ConsAxiom _ _ _ pf); apply IHismodel1.
  intros f0 i; apply mequiv; right; assumption.
Qed.

(* True iff g maps f1 and f2 to the same field *)
Definition unified_by (g : Field -> Field) f1 f2 : Prop :=
  g f1 = g f2.

(* A model respects a mapping g iff any fields unified by g are equal
   in the model *)
Definition model_respects_on flds g model :=
  forall f1 f2, In f1 flds -> In f2 (Model_fields model) ->
                unified_by g f1 f2 -> Model_proj model f1 = Model_proj model f2.

(* Shrinking flds preserves model_respects_on *)
Lemma model_respects_on_subset flds g model
      flds' (sub: incl flds' flds)
      (resp: model_respects_on flds g model) :
  model_respects_on flds' g model.
  intros f1 f2 in1 in2 unif; apply resp;
  [ apply (sub _ in1) | | ]; assumption.
Qed.


(*** Mapping models ***)

(* Map g over the field names of a model *)
Fixpoint map_model g (model:Model) : Model :=
  match model with
    | nil => nil
    | (f,elem) :: model' =>
      (g f, elem) :: map_model g model'
  end.

(* map_model maps the fields of a model *)
Lemma map_model_fields g model : Model_fields (map_model g model) = map g (Model_fields model).
  induction model.
  reflexivity.
  destruct a; unfold map_model; unfold Model_fields; fold Model_fields; fold map_model;
  unfold map; fold (map g).
  f_equal; apply IHmodel.
Qed.


(* Helper lemma for map_Model_proj *)
Lemma map_Model_projH g model f
      (resp_f: forall f2, In f2 (Model_fields model) -> unified_by g f f2 ->
                          Model_proj model f = Model_proj model f2) :
  Model_proj (map_model g model) (g f) = Model_proj model f.
  induction model.
  reflexivity.
  destruct a; destruct (Field_dec (g f0) (g f)); unfold map_model; fold map_model.
  transitivity (Model_proj ((f0, a) :: model) f0).
  unfold Model_proj; rewrite e; rewrite F_dec_true; rewrite F_dec_true; reflexivity.
  symmetry; apply resp_f; [ left; reflexivity | symmetry; assumption ].
  unfold Model_proj; unfold map_model; fold map_model; fold Model_proj.
  destruct (F_dec_false _ Field_dec _ _ n) as [ n2 e ]; rewrite e.
  destruct (Field_dec f0 f) as [ e2 | n3 ];
    [ elimtype False; rewrite e2 in n; apply n; reflexivity | ].
  apply IHmodel; intros f2 in2 unif.
  transitivity (Model_proj ((f0, a) :: model) f).
  unfold Model_proj; destruct (F_dec_false _ Field_dec _ _ n3) as [ n4 e2 ];
  rewrite e2; reflexivity.
  transitivity (Model_proj ((f0, a) :: model) f2).
  apply resp_f; [ right | ]; assumption.
  assert (f0 <> f2) as n4.
  intro e3; apply n; rewrite e3; symmetry; assumption.
  unfold Model_proj; destruct (F_dec_false _ Field_dec _ _ n4) as [ n5 e3 ];
  rewrite e3; reflexivity.
Qed.

(* Mapping lemma for Model_proj *)
Lemma map_Model_proj flds g model
      (resp: model_respects_on flds g model) f (i: In f flds) :
  Model_proj (map_model g model) (g f) = Model_proj model f.
  apply map_Model_projH; intros; apply resp; assumption.
Qed.

(* Mapping lemma for IsModelOf_RT *)
Lemma map_IsModelOf_RT g model {flds} (rectp: @RecType flds) :
  model_respects_on flds g model -> IsModelOf_RT model rectp ->
  IsModelOf_RT (map_model g model) (map_RecType g rectp).
  intros resp ismodel; induction ismodel.
  constructor.
  unfold map_RecType; fold map_RecType.
  revert rectp ismodel IHismodel; unfold Model_projT; unfold Model_projO.
  rewrite <- (map_Model_proj _ _ _ resp); [ | left; reflexivity ].
  intros. constructor. apply IHismodel.
  apply (model_respects_on_subset (f::flds)); [ apply incl_tl; apply incl_refl | assumption ].
  unfold map_RecType; fold map_RecType.
  apply (IsModelOf_RT_ConsAxiom _ _ _ pf); apply IHismodel;
  apply (model_respects_on_subset (f::flds)); [ apply incl_tl; apply incl_refl | assumption ];
  assumption.
Qed.


(*** Restricting models to a given set of fields ***)

Definition restrict_model flds (m:Model) : Model :=
  map (fun f => (f, Model_proj m f)) flds.

(* Any model is equivalent to itself restricted to the given set of fields *)
Lemma restrict_model_equiv_refl flds model :
  model_equiv_on flds model (restrict_model flds model).
  intros f i.
  induction flds.
  elimtype False; apply i.
  unfold restrict_model; unfold map;
  fold (map (fun f => (f, Model_proj model f))); fold (restrict_model flds model);
  unfold Model_proj; fold Model_proj.
  destruct (Field_dec a f).
  rewrite e; reflexivity.
  apply IHflds.
  destruct i; [ elimtype False; apply (n H) | assumption ].
Qed.

(* Projecting a field not in a restricted model (FIXME: use or remove) *)
Lemma restrict_model_not_in flds f model (not_in: ~In f flds) :
  Model_proj (restrict_model flds model) f = dummy.
  induction flds.
  reflexivity.
  unfold restrict_model; unfold map;
  fold (map (fun f => (f, Model_proj model f))); fold (restrict_model flds model);
  unfold Model_proj; fold Model_proj.
  destruct (Field_dec a f).
  elimtype False; apply not_in; left; assumption.
  apply IHflds.
  intro i; apply not_in; right; assumption.
Qed.

(* IsModelOf_RT is preserved by restricting to the fields of a record type *)
Lemma IsModelOf_RT_restrict model {flds} (rectp: @RecType flds) :
  IsModelOf_RT model rectp -> IsModelOf_RT (restrict_model flds model) rectp.
  intro ismodel; apply (IsModelOf_RT_equiv _ _ _ ismodel);
  apply restrict_model_equiv_refl.
Qed.


(*** "Unmapping" models and record types ***)

(* "Unmap" g over a model, generating a model with fields flds such
   that mapping g over the result yields model *)
Fixpoint unmap_model g model (flds : list Field) : Model :=
  match flds with
    | nil => nil
    | f :: flds' =>
      (f, Model_proj model (g f)) :: unmap_model g model flds'
  end.

(* Helper definition to "unmap" g over a record type *)
Definition unmap_RecTypeH g flds' {flds} (rectp: @RecType flds) :
  flds = map g flds' -> @RecType flds'.
  revert flds rectp; induction flds' as [ | f flds' ];
  intros flds rectp e; destruct rectp.
  apply RecType_Nil.
  elimtype False; unfold map in e; discriminate.
  elimtype False; unfold map in e; discriminate.
  elimtype False; unfold map in e; discriminate.
  apply (RecType_Cons f A); intro a; apply (IHflds' flds (rectp a)).
  unfold map in e; fold (map g) in e; injection e; intros; assumption.
  apply (RecType_ConsAxiom f P); intro pf; apply (IHflds' flds (rectp pf)).
  unfold map in e; fold (map g) in e; injection e; intros; assumption.
Defined.

(*
Program Fixpoint unmap_RecTypeH g flds' {flds} (rectp: @RecType flds) :
  flds = map g flds' -> @RecType flds' :=
  match flds', rectp in list Field, @RecType flds return flds = map g flds' -> @RecType flds' with
    | 
*)

(* The top-level definition of unmapping a record type *)
Definition unmap_RecType g {flds} (rectp: @RecType (map g flds)) : @RecType flds :=
  unmap_RecTypeH g flds rectp eq_refl.

(* Helper lemma to unfold unmap_RecType *)
Lemma unfold_unmap_RecType_Cons g f flds A (rectp : A -> @RecType (map g flds)) :
  @unmap_RecType g (f::flds) (RecType_Cons (g f) A rectp) =
  RecType_Cons f A (fun a => unmap_RecType g (rectp a)).
  reflexivity.
Qed.

(* Helper lemma to unfold unmap_RecTypeH *)
Lemma unfold_unmap_RecTypeH_Cons g f flds' flds A (rectp : A -> @RecType flds) e :
  @unmap_RecTypeH g (f::flds') ((g f)::flds) (RecType_Cons (g f) A rectp) e =
  RecType_Cons f A (fun a => @unmap_RecTypeH g flds' flds (rectp a)
                    (f_equal (fun e0 : list Field =>
                                match e0 with
                                  | nil => flds
                                  | _ :: l => l
                                end) e)).
  reflexivity.
Qed.

(* Helper lemma to unfold unmap_RecTypeH *)
Lemma unfold_unmap_RecTypeH_ConsAxiom g f flds' flds (P:Prop) (rectp : P -> @RecType flds) e :
  @unmap_RecTypeH g (f::flds') ((g f)::flds) (RecType_ConsAxiom (g f) P rectp) e =
  RecType_ConsAxiom f P (fun pf => @unmap_RecTypeH g flds' flds (rectp pf)
                    (f_equal (fun e0 : list Field =>
                                match e0 with
                                  | nil => flds
                                  | _ :: l => l
                                end) e)).
  reflexivity.
Qed.

(* Helper lemma to unfold unmap_RecType *)
Lemma unfold_unmap_RecType_ConsAxiom g f flds (P:Prop) (rectp : P -> @RecType (map g flds)) :
  @unmap_RecType g (f::flds) (RecType_ConsAxiom (g f) P rectp) =
  RecType_ConsAxiom f P (fun pf => unmap_RecType g (rectp pf)).
  reflexivity.
Qed.


(* Unmapping and then re-mapping a model is the same as a restriction *)
Lemma unmap_map_model flds g model :
  map_model g (unmap_model g model flds) = restrict_model (map g flds) model.
  induction flds.
  reflexivity.
  unfold unmap_model; fold unmap_model; unfold map_model; fold map_model.
  unfold restrict_model; unfold map; fold (map g);
  fold (map (fun f => (f, Model_proj model f))); fold (restrict_model (map g flds) model).
  f_equal; assumption.
Qed.

(* Mapping and then unmapping a record type is the identity *)
Lemma map_unmap_RecType g {flds} (rectp: @RecType flds) :
  unmap_RecType g (map_RecType g rectp) = rectp.
  induction rectp.
  reflexivity.
  unfold map_RecType; fold map_RecType; rewrite unfold_unmap_RecType_Cons;
  f_equal; apply functional_extensionality; intro a; apply H.
  unfold map_RecType; fold map_RecType; rewrite unfold_unmap_RecType_ConsAxiom;
  f_equal; apply functional_extensionality; intro pf; apply H.
Qed.

(* The fields of unmap_model are exactly the flds argument *)
Lemma unmap_model_fields g model flds :
  Model_fields (unmap_model g model flds) = flds.
  induction flds.
  reflexivity.
  unfold unmap_model; fold unmap_model; unfold Model_fields; fold Model_fields;
  f_equal; assumption.
Qed.

(* Unmapping lemma for Model_proj *)
Lemma unmap_Model_proj flds g model f :
  In f flds ->
  Model_proj (unmap_model g model flds) f = Model_proj model (g f).
  induction flds; intro i.
  elimtype False; apply i.
  unfold unmap_model; fold unmap_model; unfold Model_proj; fold Model_proj;
  destruct (Field_dec a f); [ rewrite e; reflexivity | ].
  apply IHflds.
  destruct i; [ elimtype False; apply (n H) | assumption ].
Qed.

(* An unmapped model respects g on its flds *)
Lemma unmap_model_respects flds g model :
  model_respects_on flds g (unmap_model g model flds).
  intros f1 f2 in1 in2 unif.
  rewrite unmap_Model_proj; [ | assumption ].
  rewrite unmap_Model_proj;
    [ rewrite unif; reflexivity
    | rewrite unmap_model_fields in in2; assumption ].
Qed.

(* Helper for unmapping lemma for IsModelOf *)
Lemma unmap_IsModelOf_RT_H g model flds_m {flds} (rectp: @RecType flds) :
  IsModelOf_RT model rectp ->
  forall flds' (e: flds = map g flds'),
    incl flds' flds_m ->
    IsModelOf_RT (unmap_model g model flds_m) (unmap_RecTypeH g flds' rectp e).
  intro ismodel; induction ismodel; intros flds' e sub.
  destruct flds'; [ apply IsModelOf_RT_Nil | unfold map in e; discriminate ].
  destruct flds'; unfold map in e; fold (map g) in e; [ discriminate | ].
  injection e; intros e_flds e_f;
  revert rectp ismodel IHismodel e; rewrite e_f; rewrite e_flds; intros.
  rewrite unfold_unmap_RecTypeH_Cons.
  revert rectp ismodel IHismodel; unfold Model_projT; unfold Model_projO;
  rewrite <- (unmap_Model_proj flds_m g model f0); intros.
  apply IsModelOf_RT_Cons. apply IHismodel.
  intros f' i'; apply sub; right; assumption.
  apply sub; left; reflexivity.
  destruct flds'; unfold map in e; fold (map g) in e; [ discriminate | ].
  injection e; intros e_flds e_f;
  revert rectp ismodel IHismodel e; rewrite e_f; rewrite e_flds; intros.
  rewrite unfold_unmap_RecTypeH_ConsAxiom.
  apply (IsModelOf_RT_ConsAxiom _ _ _ pf). apply IHismodel.
  intros f' i'; apply sub; right; assumption.
Qed.

(* Unmapping lemma for IsModelOf *)
Lemma unmap_IsModelOf_RT g model {flds} (rectp: @RecType flds) flds_m :
  incl flds flds_m ->
  IsModelOf_RT model (map_RecType g rectp) ->
  IsModelOf_RT (unmap_model g model flds_m) rectp.
  intros sub ismodel; rewrite <- (map_unmap_RecType g).
  apply unmap_IsModelOf_RT_H; assumption.
Qed.


(*** Model inclusion ***)

(* Model inclusion: when all models of rectp1 are models of rectp2 *)
Definition Model_incl_RT {flds1} rectp1 {flds2} rectp2 : Prop :=
  forall m, @IsModelOf_RT m flds1 rectp1 -> @IsModelOf_RT m flds2 rectp2.

(* Main theorem: Model_incl can be mapped *)
Theorem map_Model_incl_RT g {flds1} (rectp1: @RecType flds1)
        {flds2} (rectp2: @RecType flds2) :
  Model_incl_RT rectp1 rectp2 ->
  Model_incl_RT (map_RecType g rectp1) (map_RecType g rectp2).
  intros mincl model ismodel.
  assert (IsModelOf_RT (unmap_model g model (flds1 ++ flds2)) rectp1) as ismodel1;
    [ apply unmap_IsModelOf_RT; [ apply incl_appl; apply incl_refl | assumption ] | ].
  assert (IsModelOf_RT (unmap_model g model (flds1 ++ flds2)) rectp2) as ismodel2;
    [ apply mincl; assumption | ].
  assert (IsModelOf_RT (restrict_model (map g (flds1 ++ flds2)) model) (map_RecType g rectp2)) as ismodel3.
  rewrite <- unmap_map_model; apply map_IsModelOf_RT; [ | assumption ].
  apply (model_respects_on_subset (flds1 ++ flds2));
    [ apply incl_appr; apply incl_refl | ].
  apply unmap_model_respects.
  apply (IsModelOf_RT_equiv _ _ _ ismodel3).
  apply (model_equiv_on_subset (map g (flds1 ++ flds2)));
    [ rewrite map_app; apply incl_appr; apply incl_refl | ].
  apply model_equiv_on_sym. apply restrict_model_equiv_refl.
Qed.


(*** Specs: record types bundled with their fields ***)

(* A Spec is a RecType with an arbitrary field list *)
Record Spec : Type :=
  {
    spec_fields : list Field;
    spec_recType : @RecType spec_fields
  }.

(* Mapping specs *)
Definition mapSpec (g : Field -> Field) (spec: Spec) : Spec :=
  {| spec_recType := map_RecType g (spec_recType spec) |}.

(* When a Model is a model of a Spec *)
Definition IsModelOf (m: Model) (spec: Spec) : Prop :=
  IsModelOf_RT m (spec_recType spec).

(* Model inclusion: when all models of spec1 are models of spec2 *)
Definition Model_incl spec1 spec2 : Prop :=
  forall m, IsModelOf m spec1 -> IsModelOf m spec2.

(* Theorem: model inclusion commutes with mapSpec *)
Lemma map_Model_incl g spec1 spec2 :
  Model_incl spec1 spec2 -> Model_incl (mapSpec g spec1) (mapSpec g spec2).
  unfold Model_incl; unfold IsModelOf.
  intro mincl; apply map_Model_incl_RT; assumption.
Qed.


(*** Morphisms ***)

(* A morphism is a function that maps a spec to a super-spec of another *)
Definition IsMorphism (g: Field -> Field) spec1 spec2 : Prop :=
  Model_incl spec2 (mapSpec g spec1).

(* A morphism from spec1 to spec2 is a function plus a proof that the
   function is a morphism *)
Record Morphism spec1 spec2 :=
  {
    morphism_fun : Field -> Field;
    morphism_pf : IsMorphism morphism_fun spec1 spec2
  }.

Notation "s1 >=> s2" := (Morphism s1 s2) (at level 70).


(*** Transitivity of morphisms ***)

