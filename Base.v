
(*** An approach to representing Models with inductive types ***)

Require Import String.
Require Import List.

Require Export Coq.Logic.FunctionalExtensionality.

Add LoadPath "." as Specware.
Require Import Util.


(**
 ** The basic structures: signatures, models, and specs
 **)

(* A signature is a glorified record type *)
Inductive Sig : list string -> Type :=
| Sig_Nil : Sig nil
| Sig_Cons f (A : Type) flds : (A -> Sig flds) -> Sig (f :: flds)
.

(* FIXME: previous version with a requirement of uniqueness of fields *)
(*
Inductive Sig : list string -> Type :=
| Sig_Nil : Sig nil
| Sig_Cons f (A : Type) flds : ~In f flds -> (A -> Sig flds) -> Sig (f :: flds)
.
*)

(* A Model is an element of the record type denoted by a Sig *)
Inductive Model : forall {flds}, Sig flds -> Type :=
| Model_Nil : Model Sig_Nil
| Model_Cons f A a flds sig  :
    Model (flds:=flds) (sig a) ->
    Model (Sig_Cons f A flds sig)
.

(* A Spec is a partial Model of a Sig *)
Inductive Spec : forall {flds}, Sig flds -> Type :=
| Spec_Nil : Spec Sig_Nil
| Spec_ConsNone f A flds sig  :
    (forall a, Spec (flds:=flds) (sig a)) -> Spec (Sig_Cons f A flds sig)
| Spec_ConsSome f A a flds sig  :
    Spec (flds:=flds) (sig a) ->
    Spec (Sig_Cons f A flds sig)
.


(**
 ** Notions of elements of structures
 **)

(* FIXME: don't think I really need SigElem... *)
(* Proof that field f is associated with type A in signature, where A
   quantifies over all types before f in the Sig *)
Inductive SigElem (f : string) : Type -> forall {flds}, Sig flds -> Prop :=
| SigElem_Base A flds sig :
    SigElem f A (Sig_Cons f A flds sig)
| SigElem_Cons f' A' A flds sig :
    (forall (a:A'), SigElem f (A a) (sig a)) ->
    SigElem f (forall (a:A'), A a) (Sig_Cons f' A' flds sig)
.

(* Proof that field f is associated with non-dependent type A in signature *)
Inductive SigElem_nondep (f : string) A : forall {flds}, Sig flds -> Prop :=
| SigElem_nondep_Base flds sig :
    SigElem_nondep f A (Sig_Cons f A flds sig)
| SigElem_nondep_Cons f' A' flds sig :
    (forall a, SigElem_nondep f A (sig a)) ->
    SigElem_nondep f A (Sig_Cons f' A' flds sig)
.

(* Proof that field f is associated with element a of type A in model *)
Inductive ModelElem (f : string) A (a:A) : forall {flds sig}, Model (flds:=flds) sig -> Prop :=
| ModelElem_Base flds sig model :
    ModelElem f A a (Model_Cons f A a flds sig model)
| ModelElem_Cons f' A' a' flds sig model :
    ModelElem f A a model ->
    ModelElem f A a (Model_Cons f' A' a' flds sig model)
.

(* Projecting an element out of a Model *)
Fixpoint modelProj {flds sig} (model : Model (flds:=flds) sig) :
  forall f, In f flds -> { A : Type & A } :=
  match model in Model (flds:=flds) sig
        return forall f, In f flds -> { A : Type & A }
  with
    | Model_Nil => fun f in_nil => False_rect _ in_nil
    | Model_Cons f' A a _ _ model =>
      fun f in_pf =>
        match string_dec f' f with
            | left _ => existT id A a
            | right neq =>
              modelProj model f (or_proj_r _ _ neq in_pf)
        end
  end.

(* Correctness of modelProj: always returns a ModelElem *)
Lemma modelProj_correct flds sig (model : Model (flds:=flds) sig) f in_pf :
  ModelElem f (projT1 (modelProj model f in_pf))
            (projT2 (modelProj model f in_pf))
            model.
  revert f in_pf; induction model; intros.
  elimtype False; apply in_pf.
  unfold modelProj; fold (modelProj (flds:=flds) (sig:=sig a)).
  destruct (string_dec f f0).
  rewrite <- e; apply ModelElem_Base.
  apply ModelElem_Cons.
  apply IHmodel.
Qed.


(**
 ** Defining the notion of models of specs
 **)

(* A model of a Spec supplies missing fields but is otherwise equal;
   this definition requires the signatures of spec and model to be
   definitionally equal, and so is homogeneous *)
Inductive IsModel_hom : forall {flds sig}, Spec (flds:=flds) sig -> Model (flds:=flds) sig -> Prop :=
| IsModel_hom_Nil : IsModel_hom Spec_Nil Model_Nil
| IsModel_hom_ConsNone f A a flds sig spec model :
    IsModel_hom (spec a) model ->
    IsModel_hom (Spec_ConsNone f A flds sig spec)
            (Model_Cons f A a flds sig model)
| IsModel_hom_ConsSome f A a flds sig spec model :
    IsModel_hom spec model ->
    IsModel_hom (Spec_ConsSome f A a flds sig spec)
            (Model_Cons f A a flds sig model)
.

(* A model of a Spec supplies missing fields but is otherwise equal;
   this definition allows the signatures of spec and model to be
   provably, instead of definitionally, equal, and so is
   heterogeneous, similar to heterogeneous (John-Major) equality *)
Inductive IsModel_het :
  forall {flds sig_s},
    Spec (flds:=flds) sig_s ->
    forall {sig_m}, Model (flds:=flds) sig_m -> Prop :=
| IsModel_het_Nil : IsModel_het Spec_Nil Model_Nil
| IsModel_het_ConsNone f A a flds sig spec model :
    IsModel_het (spec a) model ->
    IsModel_het (Spec_ConsNone f A flds sig spec)
            (Model_Cons f A a flds sig model)
| IsModel_het_ConsSome f A a flds sig spec model :
    IsModel_het spec model ->
    IsModel_het (Spec_ConsSome f A a flds sig spec)
            (Model_Cons f A a flds sig model)
.

(* FIXME: write prove_ismodel tactic *)

(**
 ** Oooh, supermodels!
 **)

Fixpoint SuperModel {flds1 sig1} (model1 : Model (flds:=flds1) sig1)
         {flds2 sig2} (model2 : Model (flds:=flds2) sig2) : Prop :=
  match model2 with
    | Model_Nil => True
    | Model_Cons f A a flds2' sig2' model2' =>
      ModelElem f A a model1 /\ SuperModel model1 model2'
  end.

Lemma SuperModel_cons_l f A a {flds1 sig1} model1 {flds2 sig2} model2 :
  SuperModel model1 (flds2:=flds2) (sig2:=sig2) model2 ->
  SuperModel (Model_Cons f A a flds1 sig1 model1) model2.
  induction model2.
  intro; apply I.
  intro H; apply conj.
  destruct H; apply ModelElem_Cons; assumption.
  apply IHmodel2; destruct H; assumption.
Qed.

Lemma SuperModel_id {flds sig} model :
  SuperModel (flds1:=flds) (sig1:=sig) model model.
  induction model.
  apply I.
  apply conj;
    [ apply ModelElem_Base
    | apply SuperModel_cons_l; assumption ].
Qed.

Lemma SuperModel_elem {flds2 sig2} (model2 : Model (flds:=flds2) sig2)
      f A a (elem : ModelElem f A a model2)
      {flds1 sig1} (model1 : Model (flds:=flds1) sig1) :
  SuperModel model1 model2 ->
  ModelElem f A a model1.
  revert flds1 sig1 model1; induction elem; intros.
  destruct H; assumption.
  apply IHelem; destruct H; assumption.
Qed.

Lemma SuperModel_trans {flds1 sig1} (model1 : Model (flds:=flds1) sig1)
      {flds2 sig2} (model2 : Model (flds:=flds2) sig2)
      {flds3 sig3} (model3 : Model (flds:=flds3) sig3) :
  SuperModel model1 model2 -> SuperModel model2 model3 ->
  SuperModel model1 model3.
  intros super12 super23;
  revert flds1 sig1 model1 super12; induction model3; intros.
  apply I.
  apply conj.
  destruct super23; apply (SuperModel_elem model2); assumption.
  apply IHmodel3; [ destruct super23 | ]; assumption.
Qed.


(* FIXME: inductive version of SuperModel, plus (attempts!) at proofs *)
(*
Inductive SuperModel {flds1 sig1} (model1 : Model (flds:=flds1) sig1) :
  forall {flds2 sig2}, Model (flds:=flds2) sig2 -> Prop :=
| SuperModel_Nil : SuperModel model1 Model_Nil
| SuperModel_Cons f A a flds2 sig2 model2 :
    ModelElem f A a model1 ->
    SuperModel model1 model2 ->
    SuperModel model1 (Model_Cons f A a flds2 sig2 model2)
.

Lemma SuperModel_cons_l f A a {flds1 sig1} model1 {flds2 sig2} model2 :
  SuperModel model1 (flds2:=flds2) (sig2:=sig2) model2 ->
  SuperModel (Model_Cons f A a flds1 sig1 model1) model2.
  intro super; induction super.
  apply SuperModel_Nil.
  apply SuperModel_Cons;
    [ apply ModelElem_Cons | ]; assumption.
Qed.

Lemma SuperModel_id {flds sig} model :
  SuperModel (flds1:=flds) (sig1:=sig) model model.
  induction model.
  apply SuperModel_Nil.
  apply SuperModel_Cons;
    [ apply ModelElem_Base
    | apply SuperModel_cons_l; assumption ].
Qed.


(*
Lemma SuperModel_fst :
  
  SuperModel model1 (Model_Cons f A a flds2 sig2 model2)
*)


Lemma SuperModel_elem {flds2 sig2} (model2 : Model (flds:=flds2) sig2)
      f A a (elem : ModelElem f A a model2)
      {flds1 sig1} (model1 : Model (flds:=flds1) sig1) :
  SuperModel model1 model2 ->
  ModelElem f A a model1.
  revert flds1 sig1 model1; induction elem; intros.


  intro super; induction super.
  intros; inversion H.
  intros. inversion H0.



Lemma SuperModel_elem 
      {flds1 sig1} (model1 : Model (flds:=flds1) sig1)
      {flds2 sig2} (model2 : Model (flds:=flds2) sig2) :
  SuperModel model1 model2 ->
  forall f A a (elem : ModelElem f A a model2),
  ModelElem f A a model1.
  intro super; induction super; intros.
  inversion elem.
  inversion elem.

Lemma SuperModel_trans {flds1 sig1} (model1 : Model (flds:=flds1) sig1)
      {flds2 sig2} (model2 : Model (flds:=flds2) sig2)
      {flds3 sig3} (model3 : Model (flds:=flds3) sig3) :
  SuperModel model1 model2 -> SuperModel model2 model3 ->
  SuperModel model1 model3.
  intros super12 super23;
  revert flds1 sig1 model1 super12; induction super23; intros.
  apply SuperModel_Nil.


  revert flds3 sig3 model3 super23; induction super12; intros.
  inversion super23.
*)


(* FIXME: old version based on modelProj *)
(*
Inductive SuperModel {flds1 sig1} (model1 : Model (flds:=flds1) sig1) :
  forall {flds2 sig2}, Model (flds:=flds2) sig2 -> Prop :=
| SuperModel_Nil : SuperModel model1 Model_Nil
| SuperModel_Cons f in_pf flds2 sig2 model2 :
    SuperModel model1 model2 ->
    SuperModel model1
               (Model_Cons f (projT1 (modelProj model1 f in_pf))
                           (projT2 (modelProj model1 f in_pf))
                           flds2 sig2 model2)
.
*)




(**
 ** Mapping functions over structures
 **)

Fixpoint sig_map (g : string -> string) {flds} (sig : Sig flds) : Sig (map g flds) :=
  match sig in Sig flds return Sig (map g flds) with
    | Sig_Nil => Sig_Nil
    | Sig_Cons f A flds sig =>
      Sig_Cons (g f) A (map g flds) (fun a => sig_map g (sig a))
  end.

Fixpoint model_map (g : string -> string) {flds sig}
         (model : Model (flds:=flds) sig) :
  Model (flds:=map g flds) (sig_map g sig) :=
  match model in Model sig return Model (sig_map g sig) with
    | Model_Nil => Model_Nil
    | Model_Cons f A a flds sig model =>
      Model_Cons (g f) A a (map g flds) (fun a' => sig_map g (sig a'))
                 (model_map g model)
  end.

Fixpoint spec_map (g : string -> string) {flds sig}
         (spec : Spec (flds:=flds) sig) :
  Spec (flds:=map g flds) (sig_map g sig) :=
  match spec in Spec sig return Spec (sig_map g sig) with
    | Spec_Nil => Spec_Nil
    | Spec_ConsNone f A flds sig spec =>
      Spec_ConsNone (g f) A (map g flds) (fun a => sig_map g (sig a))
                    (fun a => spec_map g (spec a))
    | Spec_ConsSome f A a flds sig spec =>
      Spec_ConsSome (g f) A a (map g flds) (fun a' => sig_map g (sig a'))
                    (spec_map g spec)
  end.


FIXME HERE

(* sig_map id is the identity *)
Lemma sig_map_id {flds} (sig : Sig flds) :
  existT Sig (map id flds) (sig_map id sig) = existT Sig flds sig.
  induction sig.
  reflexivity.
  unfold map; fold (map id flds).
  unfold sig_map; fold (sig_map id (flds:=flds)).
  rewrite (functional_extensionality_dep _ _ H).

(* IsModel commutes with mapping *)
Lemma IsModel_hom_map_commutes {flds sig} (g : string -> string)
      (spec : Spec (flds:=flds) sig) (model : Model sig) :
  IsModel_hom spec model ->
  IsModel_hom (spec_map g spec) (model_map g model).
  intro ism; induction ism.
  apply IsModel_hom_Nil.
  apply IsModel_hom_ConsNone; apply IHism.
  apply IsModel_hom_ConsSome; apply IHism.
Qed.

(* IsModel commutes with mapping *)
Lemma IsModel_het_map_commutes {flds sig_s} (g : string -> string)
      (spec : Spec (flds:=flds) sig_s)
      {sig_m} (model : Model (flds:=flds) sig_m) :
  IsModel_het spec model ->
  IsModel_het (spec_map g spec) (model_map g model).
  intro ism; induction ism.
  apply IsModel_het_Nil.
  apply IsModel_het_ConsNone; apply IHism.
  apply IsModel_het_ConsSome; apply IHism.
Qed.

(* FIXME: old approach of translating models... *)

(* Models can be translated by "unapplying" a function on fields *)
(* FIXME: can only translate when we know the projected type is preserved
Fixpoint modelXlate {flds1 sig1} :
  ({f | In f flds1} -> {f | In f flds2}) ->
  forall {flds2 sig2},
    Model (flds:=flds2) sig2 ->
    Model (flds:=flds1) sig1 :=
  match sig1 in Sig flds1
        return
        ({f | In f flds1} -> {f | In f flds2}) ->
        forall {flds2 sig2},
          Model (flds:=flds2) sig2 ->
          Model (flds:=flds1) sig1
  with
    | Sig_Nil => Model_Nil
    | Sig_Cons f A flds nodup sig =>
      fun xlate flds2 sig2 model2 =>
        Model_Cons f A 
*)

(*
Inductive ModelXlates {flds2 sig2} (model2 : Model (flds:=flds2) sig2) :
  forall {flds1 sig1},
    Model (flds:=flds1) sig1 ->
    ({f | In f flds1} -> {f | In f flds2}) -> Prop :=
| ModelXlates_Nil : ModelXlates model2
*)


(**
 ** Morphisms
 **)

(* A morphism maps a spec to one with a subset of the models *)
Definition IsMorphism {flds1 sig1} (spec1 : Spec (flds:=flds1) sig1)
           {flds2 sig2} (spec2 : Spec (flds:=flds2) sig2)
           (m : string -> string) :=
  forall model2,
    IsModel_hom spec2 model2 ->
    { model1 : _ & IsModel_hom spec1 model1 & SuperModel model2 (model_map m model1) }.

Definition Morphism {flds1 sig1} (spec1 : Spec (flds:=flds1) sig1)
           {flds2 sig2} (spec2 : Spec (flds:=flds2) sig2) :=
  { m : _ & IsMorphism spec1 spec2 m }.

Definition mkMorphism {flds1 sig1} (spec1 : Spec (flds:=flds1) sig1)
           {flds2 sig2} (spec2 : Spec (flds:=flds2) sig2)
           (m : string -> string)
           (ism : IsMorphism spec1 spec2 m) : Morphism spec1 spec2 :=
  existT _ m ism.


(**
 ** Morphisms as a category
 **)

Lemma IsMorphism_id {flds sig} (spec : Spec (flds:=flds) sig) :
  IsMorphism spec spec id.
  intros model ism;
  apply (existT2 _ _ model); [ assumption | apply SuperModel_id ].

Definition mid {flds1 sig1} spec1 {flds2 sig2} spec2 :
  Morphism (flds1:=flds1) (sig1:=sig1) spec1 (flds2:=flds2) (sig2:=sig2) spec2 :=
  mkMorphism spec1 spec2 id .
