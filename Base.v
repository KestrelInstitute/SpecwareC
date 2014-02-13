
(*** An approach to representing Models with inductive types ***)

Require Import String.
Require Import List.

Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.Eqdep.

Add LoadPath "." as Specware.
Require Import Util.


(**
 ** The basic structures: signatures, models, and specs
 **)

(* A Model is an element of the record type denoted by a Sig *)
Inductive Model : forall {flds : list string}, Type :=
| Model_Nil : Model (flds:=nil)
| Model_Cons f A (a : A) flds :
    Model (flds:=flds) ->
    Model (flds:= f :: flds)
.

(* A Spec is a partial Model of a Sig *)
Inductive Spec : forall {flds : list string}, Type :=
| Spec_Nil : Spec (flds:=nil)
| Spec_ConsNone f A flds :
    (forall (a:A), Spec (flds:=flds)) -> Spec (flds:= f :: flds)
| Spec_ConsSome f A (a : A) flds :
    Spec (flds:=flds) ->
    Spec (flds:= f :: flds)
.


(**
 ** Notions of elements of structures
 **)

(* Proof that field f is associated with element a of type A in model *)
Inductive ModelElem (f : string) A (a:A) : forall {flds}, Model (flds:=flds) -> Prop :=
| ModelElem_Base flds model :
    ModelElem f A a (Model_Cons f A a flds model)
| ModelElem_Cons f' A' a' flds model :
    ModelElem f A a model ->
    ModelElem f A a (Model_Cons f' A' a' flds model)
.

(* Projecting an element out of a Model *)
Fixpoint modelProj {flds} (model : Model (flds:=flds)) :
  forall f, In f flds -> { A : Type & A } :=
  match model in Model (flds:=flds)
        return forall f, In f flds -> { A : Type & A }
  with
    | Model_Nil => fun f in_nil => False_rect _ in_nil
    | Model_Cons f' A a _ model =>
      fun f in_pf =>
        match string_dec f' f with
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
Inductive IsModel : forall {flds}, Spec (flds:=flds) -> Model (flds:=flds) -> Prop :=
| IsModel_Nil : IsModel Spec_Nil Model_Nil
| IsModel_ConsNone f A a flds spec model :
    IsModel (spec a) model ->
    IsModel (Spec_ConsNone f A flds spec)
            (Model_Cons f A a flds model)
| IsModel_ConsSome f A a flds spec model :
    IsModel spec model ->
    IsModel (Spec_ConsSome f A a flds spec)
            (Model_Cons f A a flds model)
.

(* FIXME: write prove_ismodel tactic *)

(**
 ** Oooh, supermodels!
 **)

Fixpoint SuperModel {flds1} (model1 : Model (flds:=flds1))
         {flds2} (model2 : Model (flds:=flds2)) : Prop :=
  match model2 with
    | Model_Nil => True
    | Model_Cons f A a flds2' model2' =>
      ModelElem f A a model1 /\ SuperModel model1 model2'
  end.

Lemma SuperModel_cons_l f A a {flds1} model1 {flds2} model2 :
  SuperModel model1 (flds2:=flds2) model2 ->
  SuperModel (Model_Cons f A a flds1 model1) model2.
  induction model2.
  intro; apply I.
  intro H; apply conj.
  destruct H; apply ModelElem_Cons; assumption.
  apply IHmodel2; destruct H; assumption.
Qed.

Lemma SuperModel_id {flds} model :
  SuperModel (flds1:=flds) model model.
  induction model.
  apply I.
  apply conj;
    [ apply ModelElem_Base
    | apply SuperModel_cons_l; assumption ].
Qed.

Lemma SuperModel_elem {flds2} (model2 : Model (flds:=flds2))
      {flds1} (model1 : Model (flds:=flds1))
      f A a (elem : ModelElem f A a model2) :
  SuperModel model1 model2 ->
  ModelElem f A a model1.
  revert flds1 model1; induction elem; intros.
  destruct H; assumption.
  apply IHelem; destruct H; assumption.
Qed.

Lemma SuperModel_trans {flds1} (model1 : Model (flds:=flds1))
      {flds2} (model2 : Model (flds:=flds2))
      {flds3} (model3 : Model (flds:=flds3)) :
  SuperModel model1 model2 -> SuperModel model2 model3 ->
  SuperModel model1 model3.
  intros super12 super23;
  revert flds1 model1 super12; induction model3; intros.
  apply I.
  apply conj.
  destruct super23; apply (SuperModel_elem model2); assumption.
  apply IHmodel3; [ destruct super23 | ]; assumption.
Qed.


(**
 ** Mapping functions over structures
 **)

Fixpoint model_map (g : string -> string) {flds} (model : Model (flds:=flds)) :
  Model (flds:=map g flds) :=
  match model in Model (flds:=flds) return Model (flds:=map g flds) with
    | Model_Nil => Model_Nil
    | Model_Cons f A a flds model =>
      Model_Cons (g f) A a (map g flds) (model_map g model)
  end.

Fixpoint spec_map (g : string -> string) {flds} (spec : Spec (flds:=flds)) :
  Spec (flds:=map g flds) :=
  match spec in Spec (flds:=flds) return Spec (flds:=map g flds) with
    | Spec_Nil => Spec_Nil
    | Spec_ConsNone f A flds spec =>
      Spec_ConsNone (g f) A (map g flds) (fun a => spec_map g (spec a))
    | Spec_ConsSome f A a flds spec =>
      Spec_ConsSome (g f) A a (map g flds) (spec_map g spec)
  end.

(* ModelElem commutes with mapping *)
Lemma ModelElem_map {flds} (model : Model (flds:=flds)) m f A a :
  ModelElem f A a model -> ModelElem (m f) A a (model_map m model).
  intro melem; induction melem.
  apply ModelElem_Base.
  apply ModelElem_Cons; apply IHmelem.
Qed.

(* IsModel commutes with mapping *)
Lemma IsModel_map_commutes {flds} (g : string -> string)
      (spec : Spec (flds:=flds)) (model : Model) :
  IsModel spec model ->
  IsModel (spec_map g spec) (model_map g model).
  intro ism; induction ism.
  apply IsModel_Nil.
  apply IsModel_ConsNone; apply IHism.
  apply IsModel_ConsSome; apply IHism.
Qed.

Lemma SuperModel_map_id {flds} model :
  SuperModel (flds1:=flds) model (model_map id model).
  induction model.
  apply I.
  split; [ apply ModelElem_Base | apply SuperModel_cons_l; assumption ].
Qed.

Lemma SuperModel_map_trans {flds1} (model1 : Model (flds:=flds1))
      {flds2} (model2 : Model (flds:=flds2))
      {flds3} (model3 : Model (flds:=flds3))
      m1 m2 :
  SuperModel model3 (model_map m2 model2) ->
  SuperModel model2 (model_map m1 model1) ->
  SuperModel model3 (model_map (fun x : string => m2 (m1 x)) model1).
  induction model1.
  intros; apply I.
  unfold SuperModel; unfold model_map; fold model_map;
  fold (SuperModel model3 (model_map (fun x => m2 (m1 x)) model1));
  fold (SuperModel model3 (model_map m2 model2));
  fold (SuperModel model2 (model_map m1 model1));
  intros super32 super21; destruct super21 as [ melem2 super21 ].
  split.
  apply (SuperModel_elem (model_map m2 model2)); [ apply ModelElem_map | ]; assumption.
  apply IHmodel1; assumption.
Qed.


(**
 ** Morphisms
 **)

(* A morphism maps a spec to one with a subset of the models *)
Definition IsMorphism {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2))
           (m : string -> string) :=
  forall model2,
    IsModel spec2 model2 ->
    { model1 : _ & IsModel spec1 model1 & SuperModel model2 (model_map m model1) }.

Definition Morphism {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2)) :=
  { m : _ & IsMorphism spec1 spec2 m }.

Definition mkMorphism {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2))
           (m : string -> string)
           (ism : IsMorphism spec1 spec2 m) : Morphism spec1 spec2 :=
  existT _ m ism.


(**
 ** Morphisms as a category
 **)

Lemma IsMorphism_id {flds} (spec : Spec (flds:=flds)) :
  IsMorphism spec spec id.
  intros model ism;
  apply (existT2 _ _ model); [ assumption | apply SuperModel_map_id ].
Qed.

Definition mid {flds} spec :
  Morphism (flds1:=flds) spec (flds2:=flds) spec :=
  mkMorphism spec spec id (IsMorphism_id _).

Lemma IsMorphism_trans {flds1} (spec1 : Spec (flds:=flds1))
      {flds2} (spec2 : Spec (flds:=flds2))
      {flds3} (spec3 : Spec (flds:=flds3))
      m1 m2 :
  IsMorphism spec1 spec2 m1 ->
  IsMorphism spec2 spec3 m2 ->
  IsMorphism spec1 spec3 (fun x => m2 (m1 x)).
  intros ism1 ism2 model3 ismodel3.
  destruct (ism2 model3 ismodel3) as [ model2 ismodel2 super2 ].
  destruct (ism1 model2 ismodel2) as [ model1 ismodel1 super1 ].
  apply (existT2 _ _ model1).
  assumption.
  apply (SuperModel_map_trans _ model2); assumption.
Qed.

Definition mcompose {flds1} {spec1 : Spec (flds:=flds1)}
      {flds2} {spec2 : Spec (flds:=flds2)}
      {flds3} {spec3 : Spec (flds:=flds3)}
      (morph1 : Morphism spec1 spec2)
      (morph2 : Morphism spec2 spec3) : Morphism spec1 spec3 :=
  mkMorphism spec1 spec3 (fun x => (projT1 morph2) (projT1 morph1 x))
             (IsMorphism_trans _ _ _ _ _ (projT2 morph1) (projT2 morph2)).


(**
 ** Syntax for specs and morphism
 **)

(*
FIXME HERE: figure out notations


Notation "{| |}" := Spec_Nil (at level 80).
(* Notation "{| spec |}" := spec : spec_scope. *)

Notation "{|  f  :  A  :=  a ;  spec  |}" := (Spec_ConsSome f A a _ spec) (at level 0, f at level 99).
Notation "{|  f  :  A  ;  x  ->  spec  |}" := (Spec_ConsNone f A _ (fun x => spec)) (at level 0, f at level 99, x at level 99).

Eval compute in (Spec_ConsNone "f1" nat _ (fun f1 => Spec_ConsSome "f2" nat 0 _ Spec_Nil)).

Eval compute in ({| "f2" : nat := 0; {| |} |}).

Eval compute in ({| "f1" : nat ; f1 -> "f2" : nat := 0; {| |} |}).



Eval compute in (Spec_ConsNone "f1" nat _ _ (fun f1 => Spec_ConsSome "f2" nat 0 _ (fun _ => Sig_Nil) Spec_Nil)).
*)
