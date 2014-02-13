
(*** Tactics for Refinement ***)

Add LoadPath "." as Specware.
Require Import Specware.Util.
Require Export Specware.Base.


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


(*** A Refinement step that applies an arbitrary morphism ***)

(* Applying a morphism to a refinement goal *)
Definition apply_morphism_fun {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2))
           (m12 : Morphism spec1 spec2) :
  Refinement spec2 ->
  Refinement spec1.
  intro ref2; destruct ref2 as [ flds3 spec3 m23 ].
  apply (mkRefinement _ spec3);
  apply (mcompose m12 m23).
Qed.

(* the tactic version; mostly used by other tactics *)
Ltac apply_morphism morph :=
  apply (apply_morphism_fun _ _ morph).


(*** Instantiating a field in a spec ***)

Program Definition instantiate_helper_base_fun f A a {flds} (spec : A -> Spec (flds:=flds)) :
  { spec' : Spec (flds:= f :: flds) & IsMorphism (Spec_ConsNone f A spec) spec' id } :=
  existT (fun spec' => _) (Spec_ConsSome f A a (spec a))
         (fun model2 ism2 => (existT2 _ _ model2 _ _)).
         FIXME HERE

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
