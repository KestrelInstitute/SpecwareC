
(*** An approach to representing Models with inductive types ***)

Require Import List.
Import ListNotations.

(* Require Export Coq.Logic.Eqdep. *)

Add LoadPath "." as Specware.
Require Import Specware.Util.


Section Spec.

Class FieldType (F : Set) : Set :=
  field_dec : forall (fld1 fld2 : F), {fld1=fld2} + {fld1<>fld2}.

Context `{F_dec : FieldType}.


(**
 ** The basic structures: signatures, models, and specs
 **)

(* A Model is an element of the record type denoted by a Sig *)
Inductive Model : Type :=
| Model_Nil : Model
| Model_Cons (fld:F) A (a : A) (M:Model) : Model
.

(* A Spec is a partial Model of a Sig; README: Specs are indexed with
   their fields so that the fields they contain are known: i.e., even
   an inconsistent Spec has a fixed list of fields *)
Inductive Spec : forall {flds : list F}, Type :=
| Spec_Nil : Spec (flds:=nil)
| Spec_ConsNone f A {flds} :
    (forall (a:A), Spec (flds:=flds)) -> Spec (flds:= f :: flds)
| Spec_ConsSome f A (a : A) {flds} :
    Spec (flds:=flds) ->
    Spec (flds:= f :: flds)
.

(* helper function for printing purposes *)
Definition get_fields {flds} (spec : @Spec flds) := flds.


(**
 ** Notions of elements of structures
 **)

(* Proof that field f is associated with type A in spec *)
(* FIXME: the types (and elements!) depend on earlier elements! *)
(*
Inductive SpecElem (f : F) :
  forall A, option A -> forall {flds}, Spec (flds:=flds) -> Prop :=
| SpecElem_BaseNone flds (spec : A -> Spec (flds:=flds)) :
    SpecElem f A None (Spec_ConsNone f A spec)
| SpecElem_BaseSome a flds (spec : Spec (flds:=flds)) :
    SpecElem f A (Some a) (Spec_ConsSome f A a spec)
| SpecElem_ConsNone A a f' A' flds (spec : A' -> Spec (flds:=flds)) :
    (forall a', SpecElem f A a (spec a')) ->
    SpecElem f A a (Spec_ConsNone f' A' spec)
| SpecElem_ConsSome a f' A' a' flds (spec : Spec (flds:=flds)) :
    SpecElem f A a spec ->
    SpecElem f A a (Spec_ConsSome f' A' a' spec)
.
*)

(* Get the fields of a Model *)
Fixpoint modelFields (M : Model) : list F :=
  match M with
    | Model_Nil => []
    | Model_Cons fld _ _ M' => fld :: modelFields M'
  end.

(* Proof that field f is associated with element a of type A in model *)
Inductive ModelElem (fld : F) A (a:A) : Model -> Prop :=
| ModelElem_Base (model : Model) :
    ModelElem fld A a (Model_Cons fld A a model)
| ModelElem_Cons fld' A' a' (model : Model) :
    ModelElem fld A a model ->
    ModelElem fld A a (Model_Cons fld' A' a' model)
.

(* Model_Nil has no ModelElems *)
Lemma not_ModelElem_nil (fld : F) A (a:A) :
  ModelElem fld A a Model_Nil -> False.
  assert (forall model,
            ModelElem fld A a model -> model = Model_Nil -> False).
  intros model melem e; induction melem; discriminate.
  intro melem; apply (H _ melem); reflexivity.
Qed.

(* Projecting an element out of a Model *)
(* FIXME: update or remove
Fixpoint modelProj (model : Model) :
  forall f, In f (modelFields model) -> { A : Type & A } :=
  match model in Model (flds:=flds)
        return forall f, In f flds -> { A : Type & A }
  with
    | Model_Nil => fun f in_nil => False_rect _ in_nil
    | Model_Cons f' A a _ model =>
      fun f in_pf =>
        match F_dec f' f with
            | left _ => existT id A a
            | right neq =>
              modelProj model f (or_proj_r _ _ neq in_pf)
        end
  end.

(* Correctness of modelProj: always returns a ModelElem *)
Lemma modelProj_correct flds (model : Model (flds:=flds)) f in_pf :
  ModelElem f (projT1 (modelProj model f in_pf))
            (projT2 (modelProj model f in_pf))
            model.
  revert f in_pf; induction model; intros.
  elimtype False; apply in_pf.
  unfold modelProj; fold (modelProj (flds:=flds)).
  destruct (F_dec f f0).
  rewrite <- e; apply ModelElem_Base.
  apply ModelElem_Cons.
  apply IHmodel.
Qed.
*)


(**
 ** Defining the notion of models of specs
 **)

Fixpoint IsModel (model : Model) {flds} (spec : Spec (flds:=flds)) {struct spec} : Prop :=
  match spec in Spec (flds:=flds) with
    | Spec_Nil => True
    | Spec_ConsNone f A _ specF =>
      exists a, ModelElem f A a model /\ IsModel model (specF a)
    | Spec_ConsSome f A a _ spec' =>
      ModelElem f A a model /\ IsModel model spec'
  end.

Definition IsModel_Nil model : IsModel model Spec_Nil := I.

Definition IsModel_ConsNone model f A a {flds} (spec : A -> Spec (flds:=flds))
           (melem : ModelElem f A a model) (ism : IsModel model (spec a)) :
  IsModel model (Spec_ConsNone f A spec).
  exists a; split; assumption.
Qed.

Definition IsModel_ConsSome model f A a {flds} (spec : Spec (flds:=flds))
           (melem : ModelElem f A a model) (ism : IsModel model spec) :
  IsModel model (Spec_ConsSome f A a spec).
  split; assumption.
Qed.

(* A model of a Spec contains an element for each field in the spec *)
(* README: old, inductive version
Inductive IsModel (model : Model) :
  forall {flds}, Spec (flds:=flds) -> Prop :=
| IsModel_Nil : IsModel model Spec_Nil
| IsModel_ConsNone f A a flds (spec : A -> Spec (flds:=flds)) :
    ModelElem f A a model ->
    IsModel model (spec a) ->
    IsModel model (Spec_ConsNone f A spec)
| IsModel_ConsSome f A a flds (spec : Spec (flds:=flds)) :
    ModelElem f A a model ->
    IsModel model spec ->
    IsModel model (Spec_ConsSome f A a spec)
.
*)

Lemma IsModel_nil_spec {flds} (spec : Spec (flds:=flds)) :
  IsModel Model_Nil spec -> eq_dep _ (@Spec) _ spec _ Spec_Nil.
  induction spec; intro ism.
  reflexivity.
  destruct ism as [ a sig ]; destruct sig as [ melem ism ];
  elimtype False; apply (not_ModelElem_nil _ _ _ melem).
  destruct ism as [ melem ism ];
  elimtype False; apply (not_ModelElem_nil _ _ _ melem).
Qed.


(*
Lemma IsModel_ConsNone_inversion model {flds} f A
      (spec : A -> Spec (flds:=flds)) :
  IsModel model (Spec_ConsNone f A spec) ->
  exists a, ModelElem f A a model /\ IsModel model (spec a).
  intro ism; inversion ism.
  exists a; split; [ assumption | ].
  assert (spec1 = spec).
  apply (inj_pair2_flds (inj_pair2_flds H3)).
*)

(* FIXME: write prove_ismodel tactic *)

(*
Lemma ModelElem_to_SpecElem {flds_m} (model : Model (flds:=flds_m))
      {flds_s} (spec : Spec (flds:=flds_s)) f A a :
  ModelElem f A a
*)


(**
 ** Oooh, supermodels!
 **)

Definition SuperModel (model1 : Model) (model2 : Model) : Prop :=
  forall f A a,
    ModelElem f A a model2 -> ModelElem f A a model1.

Lemma SuperModel_cons_l f A a (model1 : Model) (model2 : Model) :
  SuperModel model1 model2 ->
  SuperModel (Model_Cons f A a model1) model2.
  intros super12 f' A' a' melem2;
  apply ModelElem_Cons; apply (super12 f' A' a' melem2); assumption.
Qed.

Lemma SuperModel_id (model : Model) : SuperModel model model.
  intros f A a ism; assumption.
Qed.

Lemma SuperModel_trans model1 model2 model3 :
  SuperModel model1 model2 -> SuperModel model2 model3 ->
  SuperModel model1 model3.
  intros super12 super23 f A a melem3;
  apply (super12 f A a (super23 f A a melem3)).
Qed.


(**
 ** Field maps: finite functions on Fs
 **)

(* A FieldMap is represented as a list of pairs *)
Definition FieldMap := list (F * F).

(* The identity FieldMap *)
Definition idFM : FieldMap := [].

(* Apply a FieldMap to a F *)
Fixpoint applyFM (m : FieldMap) (str : F) : F :=
  match m with
    | [] => str
    | (str_from, str_to) :: m' =>
      if F_dec str str_from then str_to else
        applyFM m' str
  end.

(* Applying idFM is the identity *)
Lemma idFM_is_id (str : F) : applyFM idFM str = str.
  reflexivity.
Qed.

(* compose two FieldMaps, applying m1 and then m2 *)
Fixpoint composeFM (m1 m2 : FieldMap) : FieldMap :=
  match m1 with
    | [] => m2
    | (str_from, str_to) :: m1' =>
      (str_from, applyFM m2 str_to) :: composeFM m1' m2
  end.

(* composition works as expected *)
Lemma FieldMap_compose m1 m2 str :
  applyFM (composeFM m1 m2) str = applyFM m2 (applyFM m1 str).
  induction m1.
  reflexivity.
  destruct a as [ str_from str_to ]; unfold composeFM; fold composeFM.
  unfold applyFM; fold applyFM.
  destruct (F_dec str str_from).
  reflexivity.
  apply IHm1.
Qed.

(* Return the list of Fs that map to an output F *)
Fixpoint semiInvertFM (m : FieldMap) str : list F :=
  match m with
    | [] => [str]
    | (str_from, str_to) :: m' =>
      if F_dec str str_to then str_from :: semiInvertFM m' str
      else remove F_dec str_from (semiInvertFM m' str)
  end.

(* semiInvertFM returns only Fs that map back to str *)
Lemma semiInvertFM_sound m str str' :
  In str' (semiInvertFM m str) -> applyFM m str' = str.
  induction m.
  intro in_pf; destruct in_pf;
    [ rewrite H; reflexivity | destruct H ].
  destruct a as [ str_from str_to ]; unfold applyFM; fold applyFM.
  unfold semiInvertFM; fold semiInvertFM.
  destruct (F_dec str str_to); intro in_pf;
  destruct (F_dec str' str_from).
  rewrite e; reflexivity.
  apply IHm; destruct in_pf;
  [ elimtype False; apply n; rewrite H; reflexivity | assumption ].
  rewrite e in in_pf; elimtype False; apply (remove_In _ _ _ in_pf).
  apply IHm; apply (In_remove _ _ _ _ in_pf).
Qed.

(* semiInvertFM returns all Fs that map back to str *)
Lemma semiInvertFM_complete m str str' :
  applyFM m str' = str -> In str' (semiInvertFM m str).
  induction m; unfold applyFM; fold applyFM.
  intro e; left; symmetry; assumption.
  destruct a as [ str_from str_to ]; unfold semiInvertFM; fold semiInvertFM.
  destruct (F_dec str' str_from); intro eApp.
  rewrite eApp; rewrite F_dec_true; left; symmetry; assumption.
  destruct (F_dec str str_to).
  right; apply IHm; assumption.
  apply remove_not_eq; [ assumption | apply IHm; assumption ].
Qed.

(* str is always in semiInvertFM m (applyFM m str) *)
Lemma in_semiInvert_apply m str : In str (semiInvertFM m (applyFM m str)).
  apply semiInvertFM_complete; reflexivity.
Qed.


(**
 ** Mapping functions over structures
 **)

Fixpoint model_map (m : FieldMap) (model : Model) : Model :=
  match model with
    | Model_Nil => Model_Nil
    | Model_Cons f A a model =>
      Model_Cons (applyFM m f) A a (model_map m model)
  end.

Fixpoint spec_map (m : FieldMap) {flds} (spec : Spec (flds:=flds)) :
  Spec (flds:=map (applyFM m) flds) :=
  match spec in Spec (flds:=flds) return Spec (flds:=map (applyFM m) flds) with
    | Spec_Nil => Spec_Nil
    | Spec_ConsNone f A flds spec =>
      Spec_ConsNone (applyFM m f) A (fun a => spec_map m (spec a))
    | Spec_ConsSome f A a flds spec =>
      Spec_ConsSome (applyFM m f) A a (spec_map m spec)
  end.

(* mapping id over a model is the identity itself *)
Lemma model_map_id model : model_map idFM model = model.
  induction model.
  reflexivity.
  unfold model_map; fold model_map. f_equal. assumption.
Qed.


(* mapping id over a spec is the identity itself *)
Lemma spec_map_id {flds} (spec : Spec (flds:=flds)) :
  eq_dep _ (@Spec) _ (spec_map idFM spec) _ spec.
  induction spec.
  apply eq_dep_intro.
  apply (eq_dep_ctx _ (fun fs => A -> @Spec fs)
                    (map id flds) flds (fun a => spec_map idFM (s a)) s
                    _ (fun fs => f :: fs)
                    _ (fun _ spec => Spec_ConsNone f A spec)).
  apply (eq_dep_flds_fun _ F_dec); [ apply map_id | assumption ].
  apply (eq_dep_ctx _ (@Spec)
                    _ _ _ _ _ (fun fs => f :: fs) _ (fun _ => Spec_ConsSome f A a)
                    IHspec).
Qed.

(* if the result of spec_map is Spec_Nil, then the input is as well *)
Lemma spec_map_to_Nil m {flds} (spec : Spec (flds:=flds)) :
  eq_dep _ (@Spec) _ (spec_map m spec) _ Spec_Nil ->
  eq_dep _ (@Spec) _ spec _ Spec_Nil.
  induction spec; unfold spec_map; fold spec_map; intro e;
  [ reflexivity | | ];
  (assert (map (applyFM m) (f :: flds) = []);
   [ apply (eq_dep_fst e) | discriminate ]).
Qed.


(* if the result of spec_map is a Spec_ConsNone, then the input is as well *)
(* FIXME: prove or remove
Lemma spec_map_to_ConsNone m {flds} (spec : Spec (flds:=flds))
      f' A {flds'} (spec' : A -> Spec (flds:=flds')) :
  eq_dep _ (@Spec) _ (spec_map m spec) _ (Spec_ConsNone f' A spec') ->
  { f'':_ & { flds'':_ & { spec'' : A -> Spec (flds:=flds'') |
                           eq_dep _ (@Spec) _ spec
                                  _ (Spec_ConsNone f'' A spec'') }}}.
  induction spec; unfold spec_map; fold spec_map; intro e.
  assert ([] = f' :: flds'); [ apply (eq_dep_fst e) | discriminate ].
  assert (map (applyFM m) (f :: flds) = f' :: flds') as H;
    [ apply (eq_dep_fst e) | ].
  injection H; intros e_flds' e_f'.
  revert s spec' X e; rewrite <- e_f'; rewrite <- e_flds'; intros.
  assert (Spec_ConsNone (applyFM m f) A0 (fun a : A0 => spec_map m (s a))
          = Spec_ConsNone (applyFM m f) A spec');
    apply (eq_dep_eq_flds _ e).

  assert (A0 = A) as H;
    [
    | revert s X e; rewrite H; intros;
      exists f; exists flds; exists s; reflexivity ].

  [ reflexivity | | ];
  (assert (map (applyFM m) (f :: flds) = []);
   [ apply (eq_dep_fst e) | discriminate ]).
Qed.
*)

(* composing two spec_maps together *)
Lemma spec_map_comp {flds} (spec : Spec (flds:=flds)) m1 m2 :
  eq_dep _ (@Spec) _ (spec_map m2 (spec_map m1 spec)) _
         (spec_map (composeFM m1 m2) spec).
  induction spec.
  apply eq_dep_intro.
  unfold map; fold (map (applyFM m1)); fold (map (applyFM m2));
  fold (map (applyFM (composeFM m1 m2))).
  unfold spec_map; fold spec_map; rewrite FieldMap_compose.
  apply (eq_dep_ctx _ (fun fs => A -> @Spec fs)
                    (map (applyFM m2) (map (applyFM m1) flds))
                    (map (applyFM (composeFM m1 m2)) flds)
                    (fun a => spec_map m2 (spec_map m1 (s a)))
                    (fun a => spec_map (composeFM m1 m2) (s a))
                    _ (fun fs => applyFM m2 (applyFM m1 f) :: fs)
                    _ (fun _ spec => Spec_ConsNone (applyFM m2 (applyFM m1 f)) A spec)
        ).
  apply (eq_dep_flds_fun _ F_dec);
    [ rewrite map_map; apply map_ext;
      intro fld; symmetry; apply FieldMap_compose
    | assumption ].
  unfold map; fold (map (applyFM m1)); fold (map (applyFM m2));
  fold (map (applyFM (composeFM m1 m2))).
  unfold spec_map; fold spec_map; rewrite FieldMap_compose.
  apply (eq_dep_ctx _ (@Spec)
                    _ _ _ _ _
                    (fun fs => _ :: fs) _ (fun _ => Spec_ConsSome _ A a)
                    IHspec).
Qed.


(* FIXME: generalize spec_map_id and spec_map_comp into a Lemma and/or
   tactic for proving things about specs *)

(* ModelElem commutes with mapping *)
Lemma ModelElem_map model m f A a :
  ModelElem f A a model -> ModelElem (applyFM m f) A a (model_map m model).
  intro melem; induction melem.
  apply ModelElem_Base.
  apply ModelElem_Cons; apply IHmelem.
Qed.


(* SpecElem commutes with mapping *)
(*
Lemma SpecElem_map {flds} (spec : Spec (flds:=flds)) m f A a :
  SpecElem f A a spec ->
  SpecElem (m f) A a (spec_map m spec).
  intro selem; induction selem.
  apply SpecElem_BaseNone.
  apply SpecElem_BaseSome.
  unfold spec_map; fold spec_map; apply SpecElem_ConsNone; assumption.
  unfold spec_map; fold spec_map; apply SpecElem_ConsSome; assumption.
Qed.
*)

(* IsModel commutes with mapping *)
(* FIXME: prove or remove *)
(*
Lemma IsModel_map_commutes (g : F -> F)
      {flds_s} (spec : Spec (flds:=flds_s))
      {flds_m} (model : Model (flds:=flds_m)) :
  IsModel model spec ->
  IsModel (model_map g model) (spec_map g spec).
  intro ism; induction ism.
  apply IsModel_Nil.
  apply IsModel_ConsNone; apply IHism.
  apply IsModel_ConsSome; apply IHism.
Qed.
*)
  

(* FIXME: this no longer holds!
Lemma SuperModel_map_trans {flds1} (model1 : Model (flds:=flds1))
      {flds2} (model2 : Model (flds:=flds2))
      {flds3} (model3 : Model (flds:=flds3))
      m1 m2 :
  SuperModel model3 (model_map m2 model2) ->
  SuperModel model2 (model_map m1 model1) ->
  SuperModel model3 (model_map (fun x : F => m2 (m1 x)) model1).
  induction model1.
  intros super32 super21 f A a melem; inversion melem.
  unfold model_map; fold model_map;
  intros super32 super21 f' A' a' melem1.
  apply (super32 f' A' a'). apply ModelElem_map.
  apply (super21 f' A' a').

destruct super21 as [ melem2 super21 ].
  split.
  apply (SuperModel_elem (model_map m2 model2)); [ apply ModelElem_map | ]; assumption.
  apply IHmodel1; assumption.
Qed.
*)


(**
 ** Model "un-mapping", which is a weak right inverse of model
 ** mapping; i.e., model_map m (model_unmap m model) has at least all
 ** of the same model elements of model
 **)

(* Apply Model_Cons once for each field name in a list *)
Fixpoint multi_Model_Cons (flds : list F) A (a : A) model :=
  match flds with
    | [] => model
    | fld :: flds' => Model_Cons fld A a (multi_Model_Cons flds' A a model)
  end.

Lemma In_multi_Model_Cons (flds : list F) A (a : A) model f :
  In f flds -> ModelElem f A a (multi_Model_Cons flds A a model).
  induction flds; intro in_pf.
  inversion in_pf.
  destruct in_pf.
  rewrite H; apply ModelElem_Base.
  apply ModelElem_Cons; apply IHflds; assumption.
Qed.

Lemma multi_Model_Cons_ModelElem (flds : list F) A (a : A) model f A' a' :
  ModelElem f A' a' model ->
  ModelElem f A' a' (multi_Model_Cons flds A a model).
  induction flds; intro melem.
  apply melem.
  apply ModelElem_Cons; apply IHflds; assumption.
Qed.

Lemma multi_Model_Cons_un_ModelElem (flds : list F) A (a : A) model f A' a' :
  ModelElem f A' a' (multi_Model_Cons flds A a model) ->
  (In f flds /\ eq_dep _ id A a A' a') \/ ModelElem f A' a' model.
  revert A a model f A' a'; induction flds; intros.
  right; assumption.
  inversion H.
  left; split; [ left; reflexivity | reflexivity ].
  destruct (IHflds _ _ _ _ _ _ H1).
  destruct H5; left; split; [ right | ]; assumption.
  right; assumption.
Qed.

(* Un-map a model *)
Fixpoint model_unmap (m : FieldMap) (model : Model) {struct model} : Model :=
  match model with
    | Model_Nil => Model_Nil
    | Model_Cons fld A a model =>
      multi_Model_Cons (semiInvertFM m fld) A a (model_unmap m model)
  end.

(* Un-mapping the identity function is an identity *)
Lemma model_unmap_id model : model_unmap idFM model = model.
  induction model.
  reflexivity.
  unfold model_unmap; fold model_unmap.
  unfold idFM; unfold semiInvertFM;
  unfold idFM in IHmodel; rewrite IHmodel; reflexivity.
Qed.


(* applyFM and model_unmap form an adjunction w.r.t. ModelElem *)
Lemma ModelElem_spec_map_model_unmap f A a model m :
  ModelElem (applyFM m f) A a model <-> ModelElem f A a (model_unmap m model).
  split; intro melem.
  induction melem; unfold model_unmap; fold model_unmap.
  apply In_multi_Model_Cons; apply in_semiInvert_apply.
  apply multi_Model_Cons_ModelElem; assumption.
  induction model.
  inversion melem.
  unfold model_unmap in melem; fold model_unmap in melem.
  destruct (multi_Model_Cons_un_ModelElem _ _ _ _ _ _ _ melem).
  destruct H.
  rewrite H0. rewrite (semiInvertFM_sound _ _ _ H).
  apply ModelElem_Base.
  apply ModelElem_Cons; apply IHmodel; assumption.
Qed.


(* spec_map and model_unmap form an adjunction w.r.t. IsModel *)
Lemma IsModel_spec_map_model_unmap model {flds} (spec : Spec (flds:=flds)) m :
  IsModel model (spec_map m spec) <-> IsModel (model_unmap m model) spec.
  split.
  induction spec; unfold spec_map; fold spec_map; intro ism.
  apply IsModel_Nil.
  destruct ism as [ a sig ]; destruct sig as [ melem ism ].
  exists a; split;
  [ apply ModelElem_spec_map_model_unmap; assumption
  | apply H; assumption ].
  destruct ism as [ melem ism ]; split;
  [ apply ModelElem_spec_map_model_unmap; assumption
  | apply IHspec; assumption ].

  induction spec; intro ism; unfold spec_map; fold spec_map.
  apply IsModel_Nil.
  destruct ism as [ a sig ]; destruct sig as [ melem ism ].
  exists a; split;
  [ apply ModelElem_spec_map_model_unmap; assumption
  | apply H; assumption ].
  destruct ism as [ melem ism ]; split;
  [ apply ModelElem_spec_map_model_unmap; assumption
  | apply IHspec; assumption ].
Qed.


(**
 ** Morphisms
 **)

(* A morphism maps the elements of one spec to those of another *)
(*
2Definition IsMorphism_spec {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2))
           (m : F -> F) : Prop :=
  forall f A a,
    SpecElem f A a spec1 ->
    SpecElem (m f) A a spec2.
*)

(* Another def of morphisms, as being a subset mapping for models *)
Definition IsMorphism {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2))
           (m : FieldMap) : Prop :=
  forall model,
    IsModel model spec2 ->
    IsModel model (spec_map m spec1).

(* proof that the two definitions are equivalent *)
(*
Lemma IsMorphism_equiv {flds1} (spec1 : Spec (flds:=flds1))
      {flds2} (spec2 : Spec (flds:=flds2))
      (m : F -> F) :
  IsMorphism spec1 spec2 m <-> IsMorphism_models spec1 spec2 m.
  split.
*)

Inductive Morphism {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2)) :=
| mkMorphism m : IsMorphism spec1 spec2 m -> Morphism spec1 spec2.

Definition projMorph {flds1 spec1 flds2 spec2}
           (morph : @Morphism flds1 spec1 flds2 spec2) : FieldMap :=
  match morph with
    | mkMorphism m _ => m
  end.

Definition projMorph_pf {flds1 spec1 flds2 spec2}
           (morph : @Morphism flds1 spec1 flds2 spec2) :
  IsMorphism spec1 spec2 (projMorph morph) :=
  match morph with
    | mkMorphism _ pf => pf
  end.


(**
 ** Morphisms as a category
 **)

Lemma IsMorphism_id {flds} (spec : Spec (flds:=flds)) :
  IsMorphism spec spec idFM.
  intros model ism.
  rewrite spec_map_id; assumption.
Qed.

Definition mid {flds} spec :
  Morphism (flds1:=flds) spec (flds2:=flds) spec :=
  mkMorphism spec spec idFM (IsMorphism_id _).

(*
Lemma IsMorphism_map {flds1} (spec1 : Spec (flds:=flds1))
      {flds2} (spec2 : Spec (flds:=flds2)) m1 m2 :
  IsMorphism spec1 spec2 m1 ->
  forall model,
    IsModel model (spec_map m' spec2) ->
    IsModel model (spec_map (fun f => m' (m f)) spec1).
  induction spec1.
  intros; apply IsModel_Nil.
  intros.

  FIXME HERE: how to prove this?!?

  IDEA: "un-map" a model along an m, given a set of input fields:
  - un-mapping should depend only on m and flds
  - NOTE: might duplicate some fields, since model might have duplicate fields,
    so we define unmap_flds : flds -> m -> model -> list F and
    unmap : forall flds m model, Model (flds:=unmap_flds flds m model)
  - need IsModel model (spec_map m spec) <-> IsModel (unmap flds m model) spec
  - can then unmap, pass to the original IsMorphism, and then undo the unmapping

  IsMorphism (spec_map m' spec1) (spec_map m' spec2)
*)

Lemma IsMorphism_trans {flds1} (spec1 : Spec (flds:=flds1))
      {flds2} (spec2 : Spec (flds:=flds2))
      {flds3} (spec3 : Spec (flds:=flds3))
      m1 m2 :
  IsMorphism spec1 spec2 m1 ->
  IsMorphism spec2 spec3 m2 ->
  IsMorphism spec1 spec3 (composeFM m1 m2).
  intros ismorph1 ismorph2 model ism3.
  rewrite <- spec_map_comp.
  apply IsModel_spec_map_model_unmap.
  apply ismorph1.
  apply IsModel_spec_map_model_unmap.
  apply ismorph2.
  assumption.
Qed.

Definition mcompose {flds1} {spec1 : Spec (flds:=flds1)}
      {flds2} {spec2 : Spec (flds:=flds2)}
      {flds3} {spec3 : Spec (flds:=flds3)}
      (morph1 : Morphism spec1 spec2)
      (morph2 : Morphism spec2 spec3) : Morphism spec1 spec3 :=
  mkMorphism spec1 spec3 (composeFM (projMorph morph1) (projMorph morph2))
             (IsMorphism_trans _ _ _ _ _ (projMorph_pf morph1) (projMorph_pf morph2)).


End Spec.

(**
 ** Syntax for specs and morphism
 **)

(*
FIXME HERE: figure out notations
*)

(* one approach that works... *)
(*
Notation "{| |}" := Spec_Nil (at level 80).
Notation "{| spec |}" := spec.
Notation "end-spec" := Spec_Nil (at level 80).

Notation "f  :  A  :=  a ;  spec" := (Spec_ConsSome f A a spec) (at level 80, spec at level 80).
Notation "f  :  A  ;  x  =>  spec" := (Spec_ConsNone f A (fun x => spec)) (at level 80, x ident, spec at level 80).
*)


(* another approach, which always prints one {| |} pair for each level of the spec *)
(*
Notation "{|  f  :  A  :=  a ;  spec  |}" := (Spec_ConsSome f A a spec) (at level 80, f at level 99, spec at level 80).
Notation "{|  f  :  A  ;  x  =>  spec  |}" := (Spec_ConsNone f A (fun x => spec)) (at level 80, x ident, f at level 99, spec at level 80).
*)


(* README: this notation actually works (but for strings)

Delimit Scope spec_scope with spec_scope.
(* Bind Scope spec_scope with Spec. *)

Global Notation "end-spec" := Spec_Nil (at level 80).
Global Notation "{# spec #}" := (spec%spec_scope : Spec) (at level 100).

Global Notation "f  :::  A  :=  a ;  spec" := (Spec_ConsSome f A a spec) (at level 80, spec at level 80) : spec_scope.
Global Notation "f  :::  A  ;  x  =>  spec" := (Spec_ConsNone f A (fun x => spec)) (at level 80, x ident, spec at level 80) : spec_scope.

(*
Notation "{{  f  :  A  :=  a ;  spec  }}" := (Spec_ConsSome f A a (spec%spec_scope)) (at level 80, f at level 99, spec at level 80).
Notation "{{  f  :  A  ;  x  =>  spec  }}" := (Spec_ConsNone f A (fun x => (spec%spec_scope))) (at level 80, x ident, f at level 99, spec at level 80).
*)

Global Arguments Spec_ConsSome (f%string) _ _ _ (spec%spec_scope).
Global Arguments Spec_ConsNone (f%string) _ _ (spec%spec_scope).

(*
Eval compute in (Spec_ConsNone "f1" nat (fun f1 => Spec_ConsSome "f2" nat 0 Spec_Nil)).

Eval compute in ({# "f2" ::: nat := 0; end-spec #}).
Eval compute in ({# "f1" ::: nat ; f1 => "f2" ::: nat := 0; end-spec #}).
*)

*)
