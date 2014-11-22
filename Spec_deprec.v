
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
    | nil => mkAny unit tt
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
  Model_proj model f = mkAny unit tt.
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


(*** Specs ***)

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


(*** Mapping and unmapping models ***)

(* Map g over the field names of a model *)
Fixpoint map_model g (model:Model) : Model :=
  match model with
    | nil => nil
    | (f,elem) :: model' =>
      (g f, elem) :: map_model g model'
  end.

(* "Unmap" g over a model, generating a model with fields flds such
   that mapping g over the result yields model *)
Fixpoint unmap_model g model (flds : list Field) : Model :=
  match flds with
    | nil => nil
    | f :: flds' =>
      (f, Model_proj model (g f)) :: unmap_model g model flds'
  end.

(* map_model maps the fields of a model *)
Lemma map_model_fields g model : Model_fields (map_model g model) = map g (Model_fields model).
  induction model.
  reflexivity.
  destruct a; unfold map_model; unfold Model_fields; fold Model_fields; fold map_model;
  unfold map; fold (map g).
  f_equal; apply IHmodel.
Qed.


(* True iff g maps f1 and f2 to the same field *)
Definition unified_by (g : Field -> Field) f1 f2 : Prop :=
  g f1 = g f2.

(* A model respects a mapping g iff any fields unified by g are equal
   in the model *)
Definition model_respects g model :=
  forall f1 f2, In f1 (Model_fields model) -> In f2 (Model_fields model) ->
                unified_by g f1 f2 -> Model_proj model f1 = Model_proj model f2.

(* Cons preserves model_respects *)
Lemma model_respects_cons g model f elem
      (not_in: forall f', In f' (Model_fields model) -> unified_by g f f' ->
                          Model_proj model f' = elem)
      (resp: model_respects g model) : model_respects g ((f,elem)::model).
  intros f1 f2 in1 in2 unif; unfold Model_proj; fold Model_proj;
  destruct (Field_dec f f1); destruct (Field_dec f f2).
  reflexivity.
  destruct in2 as [ | in2 ]; [ elimtype False; apply n; assumption | ];
  symmetry; apply not_in; [ assumption | rewrite e; assumption ].
  destruct in1 as [ | in1 ]; [ elimtype False; apply n; assumption | ];
  apply not_in; [ assumption | rewrite e; symmetry; assumption ].
  destruct in1 as [ | in1 ]; [ elimtype False; apply n; assumption | ];
  destruct in2 as [ | in2 ]; [ elimtype False; apply n0; assumption | ];
  apply resp; assumption.
Qed.  

(* Sub-models with no duplicates preserve model_respects *)
(*
Lemma model_respects_snoc g model f elem (nodups: NoDup (Model_fields ((f,elem)::model)))
      (resp: model_respects g ((f,elem)::model)) : model_respects g model.
  intros f1 f2 in1 in2 unif.
  transitivity (Model_proj ((f, elem) :: model) f1).
  unfold Model_proj; fold Model_proj; destruct (Field_dec f f1).

  induction model;
  reflexivity.
  unfold Model_proj; fold Model_proj; destruct a; inversion nodups.
*)


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
Lemma map_Model_proj g model (resp: model_respects g model) f :
  Model_proj (map_model g model) (g f) = Model_proj model f.
  destruct (in_dec Field_dec f (Model_fields model)).
  apply map_Model_projH; intros f2 i2 unif; apply resp; assumption.

  FIXME HERE: prove that, if (g f) is in (map_model g model), then
  there must be some f' in model that g unifies with f

  assert (~ In (g f) (Model_fields (map_model g model))).
  intro in_g.

  rewrite Model_proj_not_in;
    [ rewrite Model_proj_not_in; [ reflexivity | assumption ] | ].
  rewrite map_model_fields.
  intro in_g; apply n. 



Lemma unmap_IsModelOf_RT g model {flds} (rectp: @RecType flds) :
  IsModelOf_RT model (map_RecType g rectp) ->
  IsModelOf_RT (unmap_model g model flds) rectp.


FIXME HERE: to prove that model inclusion can be mapped, prove:

- if m is a model of (mapSpec g spec) then (unmap g model (flds spec))
  is a model of spec such that any fields unified by g are equal in
  (unmap g model)

- conversely, if m is a model of spec such that all fields unified by
  g are equal, then (mapModel g model) is a model of (mapSpec g spec)




(*** Sub-specs and model inclusion ***)

(* Model inclusion: when all models of rectp1 are models of rectp2 *)
Definition Model_incl_RT {flds1} rectp1 {flds2} rectp2 : Prop :=
  forall m, @IsModelOf_RT m flds1 rectp1 -> @IsModelOf_RT m flds2 rectp2.

(* Model inclusion: when all models of spec1 are models of spec2 *)
Definition Model_incl spec1 spec2 : Prop :=
  forall m, IsModelOf m spec1 -> IsModelOf m spec2.

(* Predicate for when a RecType contains a top-level field,type pair *)
Fixpoint RecTypeContains (f:Field) (A:Type) {flds} (rectp: @RecType flds) : Prop :=
  match rectp with
    | RecType_Nil => False
    | RecType_Cons f' flds' A' rectp' =>
      (f = f' /\ (A = A'))
      \/ (forall a, RecTypeContains f A (rectp' a))
    | RecType_ConsAxiom f' flds' P rectp' =>
      (forall pf, RecTypeContains f A (rectp' pf))
  end.
(*
Inductive RecTypeContains (f:Field) (A:Type) :
  forall {flds}, @RecType flds -> Prop :=
| RecTypeContains_Base {flds} rectp :
    RecTypeContains f A (@RecType_Cons f flds A rectp)
| RecTypeContains_Cons f' {flds} A' rectp :
    (forall a, RecTypeContains f A (rectp a)) ->
    RecTypeContains f A (@RecType_Cons f' flds A' rectp)
| RecTypeContains_ConsAxiom f' {flds} P rectp :
    (forall pf, RecTypeContains f A (rectp pf)) ->
    RecTypeContains f A (@RecType_ConsAxiom f' flds P rectp)
.
*)

(* A super-spec is intuitively a spec with more fields and/or axioms *)
Fixpoint SuperRecTypeH {flds1} (rectp1: @RecType flds1) {flds2} (rectp2: @RecType flds2) : Prop :=
  match rectp2 with
    | RecType_Nil => True
    | RecType_Cons f flds2' A rectp2' =>
      (RecTypeContains f A rectp1) /\
      (forall a, SuperRecTypeH rectp1 (rectp2' a))
    | RecType_ConsAxiom f flds2' P rectp2' =>
      (forall model, IsModelOf_RT model rectp1 -> P) /\
      (forall pf, SuperRecTypeH rectp1 (rectp2' pf))
  end.
(*
Inductive SuperRecType {flds1} (rectp1: @RecType flds1) :
  forall {flds2}, @RecType flds2 -> Prop :=
| SuperRecType_Nil : SuperRecType rectp1 RecType_Nil
| SuperRecType_Cons f {flds2} A rectp2 :
    (forall a, @SuperRecType flds1 rectp1 flds2 (rectp2 a)) ->
    RecTypeContains f A rectp1 ->
    SuperRecType rectp1 (RecType_Cons f A rectp2)
| SuperRecType_ConsAxiom f {flds2} (P:Prop) rectp2 :
    (forall pf, @SuperRecType flds1 rectp1 flds2 (rectp2 pf)) ->
    (forall model, IsModelOf_RT model rectp1 -> P) ->
    SuperRecType rectp1 (RecType_ConsAxiom f P rectp2)
.
*)

Definition SuperRecType {flds1} (rectp1: @RecType flds1)
           {flds2} (rectp2: @RecType flds2) : Prop :=
  forall model, IsModelOf_RT model rectp1 -> SuperRecTypeH rectp1 rectp2.

Definition SuperSpec spec1 spec2 :=
  SuperRecType (spec_recType spec1) (spec_recType spec2).

(* Helper lemma for Soundness: if a Spec contains field f at type A
   then any model of that spec contains an element at f of type A *)
Lemma RecTypeContains_Model_proj model {flds} rectp
      (ismodelof: @IsModelOf_RT model flds rectp) :
  forall f A, RecTypeContains f A rectp -> Model_projT model f = A.
  induction ismodelof.
  intros f A rtc; elimtype False; apply rtc.
  intros f' A rtc; destruct rtc;
  [ destruct H as [ ef eA ]; rewrite ef; rewrite eA; reflexivity
  | apply IHismodelof; apply H ].
  intros; apply IHismodelof; apply H.
Qed.

(* Soundness of SuperRecTypeH: it implies model inclusion *)
Lemma SuperRecTypeH_Soundness {flds1} rectp1 {flds2} rectp2 :
  @SuperRecTypeH flds1 rectp1 flds2 rectp2 -> Model_incl_RT rectp1 rectp2.
  induction rectp2.
  intros _ model _; apply IsModelOf_RT_Nil.
  intros super model ismodelof; destruct super.
  revert rectp H H1;
  rewrite <- (RecTypeContains_Model_proj _ _ ismodelof _ _ H0); intros.
  apply IsModelOf_RT_Cons.
  apply (H _ (H1 _)); assumption.
  intros super model ismodelof; destruct super.
  apply (IsModelOf_RT_ConsAxiom _ _ _ (H0 _ ismodelof)).
  apply H; [ apply H1 | assumption ].
Qed.

Lemma SuperRecType_Soundness {flds1} rectp1 {flds2} rectp2 :
  @SuperRecType flds1 rectp1 flds2 rectp2 -> Model_incl_RT rectp1 rectp2.
  intros super model ismodelof.
  apply (SuperRecTypeH_Soundness _ _ (super model ismodelof) _ ismodelof).
Qed.

Lemma SuperSpec_Soundness spec1 spec2 :
  SuperSpec spec1 spec2 -> Model_incl spec1 spec2.
  intro super; apply SuperRecType_Soundness; apply super.
Qed.


(* Helper lemma for Completeness: if all models of a Spec contain
   field f of type A then the spec contains field f of type A *)
Lemma Model_proj_RecTypeContains f {flds} A rectp :
  (forall model, @IsModelOf_RT model flds rectp -> Model_projT model f = A) ->
  (exists model, IsModelOf_RT model rectp) ->
  RecTypeContains f A rectp.
  induction rectp.

  intros allmodels _; elimtype False; apply bool_neq_unit.
  transitivity (Model_projT [(f,mkAny boolTT trueT)] f);
    [ unfold Model_projT; unfold Model_proj;
      rewrite F_dec_true; unfold mkAny; unfold projT1; reflexivity | ].
  transitivity (Model_projT [(f,mkAny unitTT ttT)] f);
    [ 
    | unfold Model_projT; unfold Model_proj;
      rewrite F_dec_true; unfold mkAny; unfold projT1; reflexivity ].
  rewrite (allmodels _ (IsModelOf_RT_Nil _));
  rewrite (allmodels _ (IsModelOf_RT_Nil _));
  reflexivity.

  intros allmodels somemodel; destruct (Field_dec f f0).
  rewrite <- e; left; split; [ reflexivity | ].
  destruct somemodel as [ model ismodelof ].
  transitivity (Model_projT model f).
  symmetry; apply allmodels; assumption.
  apply (RecTypeContains_Model_proj _ _ ismodelof); left; split;
  [ assumption | reflexivity ].

  right. intro a0; apply H.
  admit.
  (* FIXME HERE: if RecType_Cons f A rectp is consistent, then any
     model of (rectp a) can be extended to a model of the cons *)
  destruct somemodel as [ model ismodelof ].
  exists model.
  inversion ismodelof.


Qed.

(* Completeness of SuperRecType: it is implied by model inclusion *)
Lemma SuperRecType_Completeness {flds1} rectp1 {flds2} rectp2 :
  Model_incl_RT rectp1 rectp2 -> @SuperRecType flds1 rectp1 flds2 rectp2.
  induction rectp2.
  constructor.
  intro; split.



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

Lemma map_Model_incl g spec1 spec2 :
  Model_incl spec1 spec2 -> Model_incl (mapSpec g spec1) (mapSpec g spec2).
  intro mincl.

