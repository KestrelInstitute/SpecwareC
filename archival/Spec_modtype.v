
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Minus.
Require Import Coq.Logic.FunctionalExtensionality.

(* A spec with an arbitrary T, foo, and axiom about foo being the identity *)
Module Type spec_id.
  Parameter T : Set.
  Parameter foo : T -> T.
  Axiom foo_is_id : forall x, foo x = x.
End spec_id.

(* A witness showing consistency of spec_id *)
Module spec_id_consistent : spec_id.
  Definition T := nat.
  Definition foo := fun (x:T) => x.
  Lemma foo_is_id : forall x, foo x = x.
    intros; reflexivity.
  Qed.
End spec_id_consistent.


(* A refinement of spec_id, where foo is defined as the identity *)
Module Type spec_id_foo.
  Parameter T : Set.
  Definition foo : T -> T := fun x => x.
  Parameter foo_is_id : forall x, foo x = x.

  (* README: don't prove the lemma in the spec, as this requires all
     *proofs* to be equal to this proof
  Lemma foo_is_id : forall x, foo x = x.
    intro; reflexivity.
  Qed.
   *)
End spec_id_foo.


(* a morphism : spec_id >=> spec_id_foo is a functor : spec_id_foo -> spec_id *)
Module morph_foo (s_foo : spec_id_foo) : spec_id.
  Definition T := s_foo.T.
  Definition foo := s_foo.foo.
  Definition foo_is_id := s_foo.foo_is_id.
  (*
  Lemma foo_is_id : forall x, foo x = x.
    intro; reflexivity.
  Qed.
   *)
End morph_foo.

(* README: reverse morphism not possible, because spec_id is not a
   refinement of spec_id_foo! In Coq encoding here, this is prevented
   because the module definition below does not match the spec_id_foo module
   type, as foo has the wrong definition *)
(*
Module morph_21 (s1 : spec_id) : spec_id_foo.
  Definition T := s1.T.
  Definition foo := s1.foo.
  Definition foo_is_id := s1.foo_is_id.
End morph_21.
*)

(* A refinement of spec_id where T is defined as nat *)
Module Type spec_id_T.
  Definition T : Set := nat.
  Parameter foo : T -> T.
  Axiom foo_is_id : forall x, foo x = x.
End spec_id_T.

(* A refinement of spec_id where both T and foo are defined *)
Module Type spec_id_T_foo.
  Definition T : Set := nat.
  Definition foo : T -> T := fun x => x.
  Parameter foo_is_id : forall x, foo x = x.
End spec_id_T_foo.

(* morphism from spec_id >=> spec_id_T *)
Module morph_T (s_T : spec_id_T) : spec_id.
  Definition T := s_T.T.
  Definition foo := s_T.foo.
  Definition foo_is_id := s_T.foo_is_id.
End morph_T.

(* morphism from spec_id_T >=> spec_id_T_foo *)
Module morph_foo' (s_T_foo : spec_id_T_foo) : spec_id_T.
  Definition T := s_T_foo.T.
  Definition foo := s_T_foo.foo.
  Definition foo_is_id := s_T_foo.foo_is_id.
End morph_foo'.

(* morphism from spec_id >=> spec_id_T_foo, composing morph_T and morph_foo' *)
Module morph_T_foo (s_T_foo : spec_id_T_foo) : spec_id.
  Module s_T := morph_foo' s_T_foo.
  Module s_id := morph_T s_T.
  Include s_id.
End morph_T_foo.


(*** Handling imports ***)

(* A version of spec_id_foo that imports spec_id and sets foo := fun x => x *)
Module Type spec_id_foo_I.
  (* Module Type s' := spec_id with Definition foo := fun (x:T) => x. *)
  (* Module Type s' := spec_id with Parameter T : Set with Definition foo := fun (x:spec_id.T) => x. *)

  (*
  Parameter T : Set.
  Module Type s' := spec_id with Definition foo := fun (x:T) => x.
  *)

  (* Re-declare all dependencies of definitions that change *)
  Parameter T : Set.
  (* Include (spec_id with Definition T := T with Definition foo := fun (x:T) => x). *)
  Declare Module s' : spec_id with Definition T := T with Definition foo := fun (x:T) => x.
  (* Definition foo := s'.foo. *)
End spec_id_foo_I.

(* an instance of the above module type, i.e., a witness to its consistency *)
Module spec_id_foo_I_inst : spec_id_foo_I.
  Definition T := nat.
  Module s'.
    Definition T := T.
    Definition foo := fun (x:T) => x.
    Lemma foo_is_id : forall x, foo x = x.
      intros; reflexivity.
    Qed.
  End s'.
End spec_id_foo_I_inst.

(* a morphism from spec_id to the above-defined spec *)
Module morph_foo_I (s : spec_id_foo_I) : spec_id.
  Definition T := s.T.
  Definition foo := s.s'.foo.
  Definition foo_is_id := s.s'.foo_is_id.
End morph_foo_I.


(** Another apporach: duplicate any spec which has any renamings / defs **)

Module Type renaming1_spec_id.
  Parameter T : Set.
  Definition foo : T -> T := fun x => x.
  Parameter foo_is_id : forall x, foo x = x.
End renaming1_spec_id.

(* the import then becomes trivial, as there is no "rest" of the spec *)
Module Type spec_id_foo_I2.
  Include renaming1_spec_id.
End spec_id_foo_I2.

(* a morphism from spec_id >=> spec_id_foo_I2 *)
Module morph_foo_I2 (s : spec_id_foo_I2) : spec_id.
  Definition T := s.T.
  Definition foo := s.foo.
  Definition foo_is_id := s.foo_is_id.
End morph_foo_I2.


(** An import that changes T -> U and foo -> bar **)

Module Type renaming2_spec_id.
  Parameter U : Set.
  Parameter bar : U -> U.
  Parameter bar_is_id : forall x, bar x = x.
End renaming2_spec_id.

Module Type spec_id_U.
  Include renaming2_spec_id.
End spec_id_U.

(* morphism from spec_id >=> spec_id_U *)
Module morph_U (s : spec_id_U) : spec_id.
  Definition T := s.U.
  Definition foo := s.bar.
  Definition foo_is_id := s.bar_is_id.
End morph_U.


(** A spec that imports spec_id twice, once with T/foo and once with U/bar **)
Module Type spec_id2.
  Include spec_id.
  Include spec_id_U.
End spec_id2.

(* The first morphism from spec_id >=> spec_id2 *)
Module morph_id2_proj1 (s : spec_id2) : spec_id.
  Definition T := s.T.
  Definition foo := s.foo.
  Definition foo_is_id := s.foo_is_id.
End morph_id2_proj1.

(* The second morphism from spec_id >=> spec_id2 *)
Module morph_id2_proj2 (s : spec_id2) : spec_id.
  Definition T := s.U.
  Definition foo := s.bar.
  Definition foo_is_id := s.bar_is_id.
End morph_id2_proj2.


(*** Handling propositional but not definitional equality in specs ***)

(* A spec with a more complex version of the identity function *)
Module Type spec_id_complexid.
  Definition T : Set := nat.
  Definition foo : T -> T :=
    fun x => match x with | 0 => 0 | _ => S (x - 1) end.
  Parameter foo_is_id : forall x, foo x = x.
  (*
  Lemma foo_is_id : forall x, foo x = x.
    intro x; induction x.
    reflexivity.
    unfold foo. rewrite <- pred_of_minus. unfold minus. reflexivity.
  Qed.
   *)
End spec_id_complexid.

(* morphism spec_id_foo >=> spec_id_complexid *)
Module morph_complexid (s : spec_id_complexid) : spec_id_foo.
  Definition T := s.T.
  Definition foo := fun (x:T) => x.
  (* need to prove that this definition of foo equals the expected one *)
  Lemma foo_eq : foo = s.foo.
    apply functional_extensionality.
    intros; rewrite s.foo_is_id. reflexivity.
  Qed.
  (*  *)
  Lemma foo_is_id : forall x, foo x = x.
    intros; reflexivity.
  Qed.
End morph_complexid.
