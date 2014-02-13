
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
      {flds1 sig1} (model1 : Model (flds:=flds1) sig1)
      f A a (elem : ModelElem f A a model2) :
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


(* sig_map id is the identity *)
(* FIXME: prove this or remove it *)
(*
Lemma sig_map_id {flds} (sig : Sig flds) :
  existT Sig (map id flds) (sig_map id sig) = existT Sig flds sig.
  induction sig.
  reflexivity.
  unfold map; fold (map id flds).
  unfold sig_map; fold (sig_map id (flds:=flds)).
  assert
    (existT (fun fs => A -> Sig fs) (map id flds) (fun a => sig_map id (s a))
     = existT _ flds s).
  Focus 2.
  replace
    (existT Sig (id f :: map id flds)
      (Sig_Cons (id f) A (map id flds) (fun a : A => sig_map id (s a))))
  with
    ((fun tuple =>
        existT Sig (f :: projT1 tuple) (Sig_Cons f A (projT1 tuple) (projT2 tuple)))
       (existT (fun fs => A -> Sig fs) (map id flds) (fun a => sig_map id (s a))));
    [ rewrite H0; reflexivity | ].
  reflexivity.

  assert (s = eq_rect _ (fun fs => A -> Sig fs) (fun a => sig_map id (s a)) _ (map_id _)).
  apply functional_extensionality.
  intro x.
  symmetry.

  apply eq_sigT_snd.
  apply (eq_sigT_snd (H x)).

  Print eq_sigT_snd.
  rewrite <- (eq_sigT_snd )

  Check inj_pair2.
*)


(* FIXME: prove this or remove it *)
(*
Lemma sig_map_trans {flds} f1 f2 (sig : Sig flds) :
  existT Sig _ (sig_map (fun x => f2 (f1 x)) sig)
  = existT Sig _ (sig_map f2 (sig_map f1 sig)).
*)

(* ModelElem commutes with mapping *)
Lemma ModelElem_map {flds sig} (model : Model (flds:=flds) sig) m f A a :
  ModelElem f A a model -> ModelElem (m f) A a (model_map m model).
  intro melem; induction melem.
  apply ModelElem_Base.
  apply ModelElem_Cons; apply IHmelem.
Qed.

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

Lemma SuperModel_map_id {flds sig} model :
  SuperModel (flds1:=flds) (sig1:=sig) model (model_map id model).
  induction model.
  apply I.
  split; [ apply ModelElem_Base | apply SuperModel_cons_l; assumption ].
Qed.

Lemma SuperModel_map_trans {flds1 sig1} (model1 : Model (flds:=flds1) sig1)
      {flds2 sig2} (model2 : Model (flds:=flds2) sig2)
      {flds3 sig3} (model3 : Model (flds:=flds3) sig3)
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
  apply (existT2 _ _ model); [ assumption | apply SuperModel_map_id ].
Qed.

Definition mid {flds sig} spec :
  Morphism (flds1:=flds) (sig1:=sig) spec (flds2:=flds) (sig2:=sig) spec :=
  mkMorphism spec spec id (IsMorphism_id _).

Lemma IsMorphism_trans {flds1 sig1} (spec1 : Spec (flds:=flds1) sig1)
      {flds2 sig2} (spec2 : Spec (flds:=flds2) sig2)
      {flds3 sig3} (spec3 : Spec (flds:=flds3) sig3)
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

Definition mcompose {flds1 sig1} {spec1 : Spec (flds:=flds1) sig1}
      {flds2 sig2} {spec2 : Spec (flds:=flds2) sig2}
      {flds3 sig3} {spec3 : Spec (flds:=flds3) sig3}
      (morph1 : Morphism spec1 spec2)
      (morph2 : Morphism spec2 spec3) : Morphism spec1 spec3 :=
  mkMorphism spec1 spec3 (fun x => (projT1 morph2) (projT1 morph1 x))
             (IsMorphism_trans _ _ _ _ _ (projT2 morph1) (projT2 morph2)).


(**
 ** Syntax for specs and morphism
 **)

FIXME HERE: figure out notations

Bind Scope spec_scope with Spec.

Notation "{| |}" := Spec_Nil (at level 80).
(* Notation "{| spec |}" := spec : spec_scope. *)

Notation "{|  f  :  A  :=  a ;  spec  |}" := (Spec_ConsSome f A a _ (fun _ => _) spec) (at level 80, f at level 99).
Notation "{|  f  :  A  ;  x  ->  spec  |}" := (Spec_ConsNone f A _ _ (fun x => spec)) (at level 80, f at level 99, x at level 99).

Eval compute in (Spec_ConsNone "f1" nat _ _ (fun f1 => Spec_ConsSome "f2" nat 0 _ (fun _ => Sig_Nil) Spec_Nil)).

Eval compute in ({| "f2" : nat := 0; {| |} |}).

Eval compute in ({| "f1" : nat ; f1 -> "f2" : nat := 0; {| |} |}).



Eval compute in (Spec_ConsNone "f1" nat _ _ (fun f1 => Spec_ConsSome "f2" nat 0 _ (fun _ => Sig_Nil) Spec_Nil)).
