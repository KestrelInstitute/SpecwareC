
(*** Tactics for Refinement ***)

Add LoadPath "." as Specware.
Require Import Specware.Util.
Require Export Specware.Base.

Import ListNotations.
Require Export Coq.Logic.Eqdep.


(*** Refinements and helper defs ***)

(* a Refinement of a spec is another spec and a morphism to it *)
Inductive Refinement {flds} (spec : Spec (flds:=flds)) : Type :=
| mkRefinement {flds'} (spec' : Spec (flds:=flds')) (morph : Morphism spec spec')
  : Refinement spec.

(* An existential type for a spec that hides the fields when printing *)
Inductive SomeSpec : Type :=
| mkSomeSpec {flds} (spec : Spec (flds:=flds)) : SomeSpec.

(* Extracting the destination spec of a Refinement *)
Definition refinementSpec {flds} {spec : Spec (flds:=flds)} (ref : Refinement spec) : SomeSpec :=
  match ref with
    | mkRefinement _ spec' _ => mkSomeSpec spec'
  end.

(*** The simplest refinement tactic: finish refinement (you're done) ***)

(* The identity refinement *)
Definition id_refinement {flds} spec : Refinement (flds:=flds) spec :=
  mkRefinement spec spec (mid _).

(* the tactic the ends refinement, giving the current spec being refined as the output *)
Ltac end_refine := apply id_refinement.


(*** A Refinement step that applies a morphism ***)

(* Applying a morphism to prove a refinement goal *)
Definition apply_morphism_fun {flds1} {spec1 : Spec (flds:=flds1)}
           {flds2} {spec2 : Spec (flds:=flds2)}
           (m12 : Morphism spec1 spec2) :
  Refinement spec2 ->
  Refinement spec1.
  intro ref2; destruct ref2 as [ flds3 spec3 m23 ].
  apply (mkRefinement _ spec3);
  apply (mcompose m12 m23).
Defined.

(* The above as a tactic, so we don't have to write "apply apply_morphism" *)
Ltac apply_morphism morph := apply (apply_morphism_fun morph).


(*** Refinement of sub-specs ***)

Definition IsMorphism_ConsNone f A {flds1} spec1 {flds2} spec2 m :
  (forall a, @IsMorphism flds1 (spec1 a) flds2 (spec2 a) m) ->
  IsMorphism (Spec_ConsNone f A spec1) (Spec_ConsNone (applyFM m f) A spec2) m.
  intros ismorph model ism.
  destruct ism as [ a sig ]; destruct sig as [ melem ism ].
  exists a; split; [ | apply ismorph ]; assumption.
Qed.

Definition IsMorphism_ConsSome f A a {flds1} spec1 {flds2} spec2 m :
  @IsMorphism flds1 spec1 flds2 spec2 m ->
  IsMorphism (Spec_ConsSome f A a spec1) (Spec_ConsSome (applyFM m f) A a spec2) m.
  intros ismorph model ism.
  destruct ism as [ melem ism ]; split; [ | apply ismorph ]; assumption.
Qed.


(*** Instantiating a field in a spec ***)

Lemma IsMorphism_instantiate_base f A a {flds} (spec : A -> Spec (flds:=flds)) :
  IsMorphism (Spec_ConsNone f A spec) (Spec_ConsSome f A a (spec a)) idFM.
  intros model ism; destruct ism.
  exists a; split;
  [ rewrite idFM_is_id | rewrite spec_map_id ]; assumption.
Qed.

Definition instantiate_field_base f {A} (a:A) {flds} (spec : A -> @Spec flds) :
  { spec' : @Spec (f :: flds) | IsMorphism (Spec_ConsNone f A spec) spec' idFM } :=
  existT _ (Spec_ConsSome f A a (spec a)) (IsMorphism_instantiate_base _ _ _ _).

(*
Definition instantiate_field_base f A a {flds} {spec : A -> Spec (flds:=flds)} :
  Refinement (Spec_ConsSome f A a (spec a)) ->
  Refinement (Spec_ConsNone f A spec) :=
  apply_morphism_fun (mkMorphism _ _ idFM (IsMorphism_instantiate_base _ _ _ _)).
*)

Lemma IsMorphism_instantiate_ConsNone f A {flds} (spec1 : A -> Spec (flds:=flds))
      (spec2 : A -> Spec (flds:=flds)) :
  (forall a, IsMorphism (spec1 a) (spec2 a) idFM) ->
  IsMorphism (Spec_ConsNone f A spec1) (Spec_ConsNone f A spec2) idFM.
  intros ismorph model ism;
  destruct ism as [ a sig ]; destruct sig as [ melem ism ].
  exists a; split;
  [ rewrite idFM_is_id | apply ismorph ]; assumption.
Qed.

Definition instantiate_field_None f A {flds} {spec : A -> @Spec flds}
  (fn : forall a, { spec' : @Spec flds |
                    IsMorphism (spec a) spec' idFM }) :
  { spec' : @Spec (f :: flds) | IsMorphism (Spec_ConsNone f A spec) spec' idFM } :=
  existT _ (Spec_ConsNone f A (fun a => projT1 (fn a)))
         (IsMorphism_instantiate_ConsNone
            f A spec _
            (fun a => projT2 (fn a))).

Lemma IsMorphism_instantiate_ConsSome f A a {flds} (spec1 : Spec (flds:=flds))
      (spec2 : Spec (flds:=flds)) :
  IsMorphism spec1 spec2 idFM ->
  IsMorphism (Spec_ConsSome f A a spec1) (Spec_ConsSome f A a spec2) idFM.
  intros ismorph model ism;
  destruct ism as [ melem ism ].
  split; [ rewrite idFM_is_id | apply ismorph ]; assumption.
Qed.

Definition instantiate_field_Some f A a {flds} {spec : @Spec flds}
  (rest : { spec' : @Spec flds | IsMorphism spec spec' idFM }) :
  { spec' : @Spec (f :: flds) | IsMorphism (Spec_ConsSome f A a spec) spec' idFM } :=
  existT _ (Spec_ConsSome f A a (projT1 rest))
         (IsMorphism_instantiate_ConsSome f A a spec _ (projT2 rest)).


(* A helper tactic which repeatedly tries to apply instantiate_field_* above *)
Ltac instantiate_helper f val :=
  repeat (apply (instantiate_field_base f val) ||
          apply instantiate_field_None ||
          apply instantiate_field_Some).

FIXME HERE: figure out how to write this stupid tactic!

(* The tactic itself *)
Ltac instantiate_field f val :=
  match goal with
    | |- @Refinement ?flds ?spec =>
      let H := fresh "H" in
      let spec' := fresh "spec" in
      let ism := fresh "isMorph" in
      assert ({ spec' : @Spec flds | IsMorphism spec spec' id }) as H;
        [ instantiate_helper f val | ];
      destruct H as [ spec' ism ];
      apply_morphism (mkMorphism spec spec' id ism)
    | _ => fail "Not a refinement goal!"
  end.

Definition test_spec_fun :=
  Spec_ConsNone "T" Set (fun T =>
  Spec_ConsNone "f" (T -> T) (fun f =>
  Spec_Nil)).

(* Set Ltac Debug. *)

Definition test_spec_id : Refinement test_spec_fun.
  assert ({ spec' : @Spec ["T"%string; "f"%string ] | IsMorphism test_spec_fun spec' idFM }) as H.
  instantiate_helper ("T"%string) (fun (x:nat) => x).

  instantiate_field ("f"%string) (fun T (x:T) => x).

Eval compute in (get_fields test_spec_fun).

Definition test_spec_id : Refinement test_spec_fun.
  assert ({ spec' : @Spec ["T"%string; "f"%string ] | IsMorphism test_spec_fun spec' idFM }) as H.
  apply instantiate_field_None; intro a.
  apply (instantiate_field_base (fun x => x)).
  destruct H as [ spec' ismorph ]; apply_morphism (mkMorphism _ _ _ ismorph).
  end_refine.
Defined.

Eval compute in (refinementSpec test_spec_id).



Definition test_spec_id :=
  Spec_ConsNone "T" Set (fun T =>
  Spec_ConsSome "idT" (T -> T) (fun t => t)
  Spec_Nil).

Definition test_spec_id_nat :=
  Spec_ConsSome "T" Set nat (
  Spec_ConsSome "idT" (nat -> nat) (fun t => t)
  Spec_Nil).

(* FIXME: cannot get type-class resolution to work here... *)
(*
Section instantiation.

  Class InstantiatesTo
        {flds1} (spec1 : Spec (flds:=flds1))
        {flds2} (spec2 : Spec (flds:=flds2)) : Prop :=
    instantiation_ismorph_id : IsMorphism spec1 spec2 idFM.

  Variables (flds:list string) (fld:string) (A:Type) (a:A)
            (spec:A -> Spec (flds:=flds)).

  Global Instance InstantiatesTo_Base :
    InstantiatesTo (Spec_ConsNone fld A spec) (Spec_ConsSome fld A a (spec a)).
  intros model ism; destruct ism.
  exists a; split;
  [ rewrite idFM_is_id | rewrite spec_map_id ]; assumption.
  Qed.

  (*
  Definition test1 :
    InstantiatesTo (Spec_ConsNone fld A spec) (Spec_ConsSome fld A a (spec a))
    := instantiation_ismorph_id.
   *)

End instantiation.
*)


(*
Program Definition instantiate_helper_step_ConsNone
           f A {flds} (spec : A -> Spec (flds:=flds))
           (F : forall a,
                  { spec' : Spec (flds:=flds) & IsMorphism (spec a) spec' id }) :
  { spec' : Spec (flds:= f :: flds)
                 & IsMorphism (Spec_ConsNone f A spec) spec' id } :=
  existT (fun spec' => IsMorphism _ spec' id)
         ({# f ::: A ; a => projT1 (F a) #})
         (fun model2 ism2 =>
            existT2 (fun _ => _) (fun _ => _) model2
                    _ _).
Obligation 1.
apply (IsModel_ConsNone)

  apply (match )

Definition instantiate_helper_step_ConsSome
           f A a {flds} (spec : A -> Spec (flds:=flds)) :
  { spec' : Spec (flds:= f :: flds) & IsMorphism (Spec_ConsNone f A spec) spec' id } :
*)

Ltac instantiate_field f val :=
  match goal with
    | |- Refinement ?flds ?spec =>
      let H := fresh "H" in
      let spec' := fresh "spec" in
      let ism := fresh "isMorph" in
      assert ({ spec' : Spec (flds:=flds) | IsMorphism spec spec' id }) as H; [ instantiate_helper f val spec | ];
      destruct H as [ spec' ism ];
      apply (apply_morphism (mkMorphism spec spec' id ism))
    | _ => fail "Not a refinement goal!"
  end.
