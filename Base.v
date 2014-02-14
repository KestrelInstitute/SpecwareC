
(*** An approach to representing Models with inductive types ***)

Require Export String.
Require Import List.

(* Require Export Coq.Logic.Eqdep. *)

Add LoadPath "." as Specware.
Require Import Specware.Util.


(**
 ** The basic structures: signatures, models, and specs
 **)

(* A Model is an element of the record type denoted by a Sig *)
Inductive Model : forall {flds : list string}, Type :=
| Model_Nil : Model (flds:=nil)
| Model_Cons f A (a : A) {flds} :
    Model (flds:=flds) ->
    Model (flds:= f :: flds)
.

(* A Spec is a partial Model of a Sig *)
Inductive Spec : forall {flds : list string}, Type :=
| Spec_Nil : Spec (flds:=nil)
| Spec_ConsNone f A {flds} :
    (forall (a:A), Spec (flds:=flds)) -> Spec (flds:= f :: flds)
| Spec_ConsSome f A (a : A) {flds} :
    Spec (flds:=flds) ->
    Spec (flds:= f :: flds)
.


(**
 ** Notions of elements of structures
 **)

(* Proof that field f is associated with type A in spec *)
(* FIXME: the types (and elements!) depend on earlier elements! *)
(*
Inductive SpecElem (f : string) :
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


(* Proof that field f is associated with element a of type A in model *)
Inductive ModelElem (f : string) A (a:A) : forall {flds}, Model (flds:=flds) -> Prop :=
| ModelElem_Base flds (model : Model (flds:=flds)) :
    ModelElem f A a (Model_Cons f A a model)
| ModelElem_Cons f' A' a' flds (model : Model (flds:=flds)) :
    ModelElem f A a model ->
    ModelElem f A a (Model_Cons f' A' a' model)
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

(* A model of a Spec contains an element for each field in the spec *)
Inductive IsModel {flds_m} (model : Model (flds:=flds_m)) :
  forall {flds_s}, Spec (flds:=flds_s) -> Prop :=
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

(* FIXME: write prove_ismodel tactic *)

(*
Lemma ModelElem_to_SpecElem {flds_m} (model : Model (flds:=flds_m))
      {flds_s} (spec : Spec (flds:=flds_s)) f A a :
  ModelElem f A a
*)


(**
 ** Oooh, supermodels!
 **)

Definition SuperModel {flds1} (model1 : Model (flds:=flds1))
         {flds2} (model2 : Model (flds:=flds2)) : Prop :=
  forall f A a,
    ModelElem f A a model2 -> ModelElem f A a model1.

Lemma SuperModel_cons_l f A a {flds1} (model1 : Model (flds:=flds1))
      {flds2} (model2 : Model (flds:=flds2)) :
  SuperModel model1 model2 ->
  SuperModel (Model_Cons f A a model1) model2.
  intros super12 f' A' a' melem2;
  apply ModelElem_Cons; apply (super12 f' A' a' melem2); assumption.
Qed.

Lemma SuperModel_id {flds} (model : Model (flds:=flds)) :
  SuperModel model model.
  intros f A a ism; assumption.
Qed.

Lemma SuperModel_trans {flds1} (model1 : Model (flds:=flds1))
      {flds2} (model2 : Model (flds:=flds2))
      {flds3} (model3 : Model (flds:=flds3)) :
  SuperModel model1 model2 -> SuperModel model2 model3 ->
  SuperModel model1 model3.
  intros super12 super23 f A a melem3;
  apply (super12 f A a (super23 f A a melem3)).
Qed.


(**
 ** Mapping functions over structures
 **)

Fixpoint model_map (g : string -> string) {flds} (model : Model (flds:=flds)) :
  Model (flds:=map g flds) :=
  match model in Model (flds:=flds) return Model (flds:=map g flds) with
    | Model_Nil => Model_Nil
    | Model_Cons f A a flds model =>
      Model_Cons (g f) A a (model_map g model)
  end.

Fixpoint spec_map (g : string -> string) {flds} (spec : Spec (flds:=flds)) :
  Spec (flds:=map g flds) :=
  match spec in Spec (flds:=flds) return Spec (flds:=map g flds) with
    | Spec_Nil => Spec_Nil
    | Spec_ConsNone f A flds spec =>
      Spec_ConsNone (g f) A (fun a => spec_map g (spec a))
    | Spec_ConsSome f A a flds spec =>
      Spec_ConsSome (g f) A a (spec_map g spec)
  end.

(* mapping id over a model is the identity itself *)
Lemma model_map_id {flds} (model : Model (flds:=flds)) :
  eq_dep _ (@Model) (map id flds) (model_map id model) flds model.
  induction model.
  apply eq_dep_intro.
  apply (eq_dep_ctx _ (@Model)
                    _ _ _ _ _ (fun fs => f :: fs) _ (fun _ => Model_Cons f A a)
                    IHmodel).
Qed.


(* mapping id over a spec is the identity itself *)
Lemma spec_map_id {flds} (spec : Spec (flds:=flds)) :
  eq_dep _ (@Spec) _ (spec_map id spec) _ spec.
  induction spec.
  apply eq_dep_intro.
  apply (eq_dep_ctx _ (fun fs => A -> @Spec fs)
                    (map id flds) flds (fun a => spec_map id (s a)) s
                    _ (fun fs => f :: fs)
                    _ (fun _ spec => Spec_ConsNone f A spec)).
  apply eq_dep_flds_fun; [ apply map_id | assumption ].
  apply (eq_dep_ctx _ (@Spec)
                    _ _ _ _ _ (fun fs => f :: fs) _ (fun _ => Spec_ConsSome f A a)
                    IHspec).
Qed.

(* composing two spec_maps together *)
Lemma spec_map_comp {flds} (spec : Spec (flds:=flds)) m1 m2 :
  eq_dep _ (@Spec) _ (spec_map m2 (spec_map m1 spec)) _
         (spec_map (fun x => m2 (m1 x)) spec).
  induction spec.
  apply eq_dep_intro.
  apply (eq_dep_ctx _ (fun fs => A -> @Spec fs)
                    (map m2 (map m1 flds)) (map (fun x => m2 (m1 x)) flds)
                    (fun a => spec_map m2 (spec_map m1 (s a)))
                    (fun a => spec_map (fun x => m2 (m1 x)) (s a))
                    _ (fun fs => m2 (m1 f) :: fs)
                    _ (fun _ spec => Spec_ConsNone (m2 (m1 f)) A spec)
        ).
  apply eq_dep_flds_fun; [ apply map_map | assumption ].
  apply (eq_dep_ctx _ (@Spec)
                    _ _ _ _ _
                    (fun fs => _ :: fs) _ (fun _ => Spec_ConsSome _ A a)
                    IHspec).
Qed.

(* FIXME: generalize spec_map_id and spec_map_comp into a Lemma and/or
   tactic for proving things about specs *)

(* ModelElem commutes with mapping *)
Lemma ModelElem_map {flds} (model : Model (flds:=flds)) m f A a :
  ModelElem f A a model -> ModelElem (m f) A a (model_map m model).
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
Lemma IsModel_map_commutes (g : string -> string)
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
  SuperModel model3 (model_map (fun x : string => m2 (m1 x)) model1).
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
 ** Morphisms
 **)

(* A morphism maps the elements of one spec to those of another *)
(*
Definition IsMorphism_spec {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2))
           (m : string -> string) : Prop :=
  forall f A a,
    SpecElem f A a spec1 ->
    SpecElem (m f) A a spec2.
*)

(* Another def of morphisms, as being a subset mapping for models *)
Definition IsMorphism {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2))
           (m : string -> string) : Prop :=
  forall flds_m (model : Model (flds:=flds_m)),
    IsModel model spec2 ->
    IsModel model (spec_map m spec1).

(* proof that the two definitions are equivalent *)
(*
Lemma IsMorphism_equiv {flds1} (spec1 : Spec (flds:=flds1))
      {flds2} (spec2 : Spec (flds:=flds2))
      (m : string -> string) :
  IsMorphism spec1 spec2 m <-> IsMorphism_models spec1 spec2 m.
  split.
*)

Definition Morphism {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2)) :=
  { m : _ | IsMorphism spec1 spec2 m }.

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
  intros flds_m model ism.
  apply
    (eq_dep_rect
       _ _ _ _
       (fun fs sp => IsModel model sp)
       ism _ _
       (eq_dep_sym _ _ _ _ _ _ (spec_map_id spec))
    ).
Qed.

Definition mid {flds} spec :
  Morphism (flds1:=flds) spec (flds2:=flds) spec :=
  mkMorphism spec spec id (IsMorphism_id _).

Lemma IsMorphism_map {flds1} (spec1 : Spec (flds:=flds1))
      {flds2} (spec2 : Spec (flds:=flds2)) m m' :
  IsMorphism spec1 spec2 m ->
  forall flds_m (model : Model (flds:=flds_m)),
    IsModel model (spec_map m' spec2) ->
    IsModel model (spec_map (fun f => m' (m f)) spec1).
  induction spec1.
  intros; apply IsModel_Nil.
  intros.

  FIXME HERE: how to prove this?!?

  IDEA: "un-map" a model along an m, given a set of input fields:
  - un-mapping should depend only on m and flds
  - NOTE: might duplicate some fields, since model might have duplicate fields,
    so we define unmap_flds : flds -> m -> model -> list string and
    unmap : forall flds m model, Model (flds:=unmap_flds flds m model)
  - need IsModel model (spec_map m spec) <-> IsModel (unmap flds m model) spec
  - can then unmap, pass to the original IsMorphism, and then undo the unmapping

  IsMorphism (spec_map m' spec1) (spec_map m' spec2)

Lemma IsMorphism_trans {flds1} (spec1 : Spec (flds:=flds1))
      {flds2} (spec2 : Spec (flds:=flds2))
      {flds3} (spec3 : Spec (flds:=flds3))
      m1 m2 :
  IsMorphism spec1 spec2 m1 ->
  IsMorphism spec2 spec3 m2 ->
  IsMorphism spec1 spec3 (fun x => m2 (m1 x)).
  intros ismorph1 ismorph2 flds_m model ismodel. Check spec_map_comp.
  assert (IsModel model (spec_map m2 (spec_map m1 spec1))).
  apply (ismorph2 flds_m ).
  apply
    (eq_dep_rect
       _ _ _ _
       (fun fs sp => IsModel model sp)
       ismodel _ _
       (spec_map_comp spec1 m1 m2)).

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
