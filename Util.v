(***
 *** Utility functions and lemmas
 ***)

Require Export String.
Require Export List.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.EqdepFacts.
Require Export Coq.Logic.Eqdep_dec.


(* helper function for eliminating ors *)
Definition or_proj_r A B : ~A -> A \/ B -> B.
  intros not_A or; destruct or.
  elimtype False; apply not_A; assumption.
  assumption.
Qed.

(* helper function for eliminating ors *)
Definition or_proj_l A B : ~B -> A \/ B -> A.
  intros not_B or; destruct or.
  assumption.
  elimtype False; apply not_B; assumption.
Qed.


(*** UIP (and friends) for lists of strings ***)

(* decidability of equality for lists of strings *)
Module DecidableSetListString.
  Definition U := list string.
  Lemma eq_dec : forall x y:U, {x=y} + {x<>y}.
    apply list_eq_dec; apply string_dec.
  Qed.
End DecidableSetListString.

(* EqDep module for lists of strings *)
Module EqDepListString := DecidableEqDep (DecidableSetListString).

Definition UIP_flds flds1 flds2 (p1 p2 : flds1 = flds2) : p1 = p2 :=
  EqDepListString.UIP flds1 flds2 p1 p2.

Definition UIP_refl_flds flds (p : flds = flds) : p = eq_refl :=
  EqDepListString.UIP_refl flds p.

Definition eq_dep_eq_flds :
  forall P {flds} {x y : P flds}, eq_dep _ P flds x flds y -> x = y :=
  EqDepListString.eq_dep_eq.

(* inj_pair2 for lists of strings *)
Definition inj_pair2_flds {flds : list string} {A a b} :
  existT A flds a = existT A flds b -> a = b :=
  EqDepListString.inj_pairT2 A flds a b.


(*** helpers for proving eq_dep goals ***)

Lemma eq_dep_commute A B (a1 a2 : A) (b1 : B a1) (b2 : B a2)
      C (f : forall x (y : B x), C x y) :
  eq_dep _ _ a1 b1 a2 b2 ->
  eq_dep _ (fun tup => C (projT1 tup) (projT2 tup))
         (existT B a1 b1) (f a1 b1)
         (existT B a2 b2) (f a2 b2).
  intro e; induction e.
  apply eq_dep_intro.
Qed.

Lemma eq_dep_ctx A B (a1 a2 : A) (b1 : B a1) (b2 : B a2)
      A' (f : A -> A')
      B' (g : forall x, B x -> B' (f x)) :
  eq_dep _ _ a1 b1 a2 b2 ->
  eq_dep _ _ (f a1) (g a1 b1) (f a2) (g a2 b2).
  intro e; induction e.
  apply eq_dep_intro.
Qed.

Lemma eq_dep_flds_fun U B (a1 a2 : list string)
      (b1 : U -> B a1) (b2 : U -> B a2) (e : a1 = a2) :
  (forall u, eq_dep _ B a1 (b1 u) a2 (b2 u)) ->
  eq_dep _ (fun a => U -> B a) a1 b1 a2 b2.
  revert b1 b2; rewrite e; intros.
  rewrite (functional_extensionality_dep
             _ _
             (fun u' => eq_dep_eq_flds _ (H u'))).
  apply eq_dep_intro.
Qed.
