
Add LoadPath "../theories" as Specware.
Require Import Specware.SpecwareC.

Require Import Coq.Arith.Arith_base.


(***
 *** Syntax for a spec; creates a sequence of type classes a-la Spitters and van
 *** der Weegen
 ***)

Spec Monoid.

Spec Variable T : Type.
Spec Variable m_zero : T.
Spec Variable m_plus : (T -> T -> T).

Spec Axiom m_zero_left : (forall x, m_plus m_zero x = x).
Spec Axiom m_zero_right : (forall x, m_plus x m_zero = x).
Spec Axiom m_plus_assoc : (forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z).

Spec End Monoid.


(***
 *** The results are: a type-class; a Spec inductive object that represents the
 *** type-class; and a proof that the two are isomorphic.
 ***)

Print Monoid.Monoid.
Print Monoid.Monoid__Spec.
(* Print Monoid.Monoid__Iso. *)


(***
 *** We can prove theorems in the new Monoid spec, by adding an assumption of a
 *** model of Monoid to the current context, and then just use the variables and
 *** axioms like normal defined names.
 ***)

Section Monoid_Thms.
Import Monoid.
Context `{Monoid}.
Lemma left_id_uniq (x:T) : (forall y, m_plus x y = y) -> x = m_zero.
  intros left_id.
  rewrite <- (left_id m_zero).
  rewrite m_zero_right.
  reflexivity.
Qed.

End Monoid_Thms.


(***
 *** The point of the Spec object created above for Monoid is that it allows us
 *** operate (indirectly) on the Monoid type-class as a first-class object in
 *** the Coq theory. As a simple example, the following Group spec imports the
 *** Monoid spec, but with all names starting with "m_" replaced by names
 *** starting with "g_".
 ***)

Spec Group.

Spec Import Monoid {m_% +-> g_%}.

Spec Variable g_inv : (T -> T).
Spec Axiom g_inv_left : (forall x, g_plus (g_inv x) x = g_zero).
Spec Axiom g_inv_right : (forall x, g_plus x (g_inv x) = g_zero).

Spec End Group.


(***
 *** We can see the type-class that was created:
 ***)

Print Group.Group.


(***
 *** We can prove theorems in the Group spec using theorems we proved in the
 *** context of the Monoid spec; e.g., left_id_uniq, used below, was proved
 *** above for Monoids. (We prove it again with a different name just so that we
 *** can apply it directly, as a demo.)
 ***)

Section Group_Thms.
Import Group.
Context `{Group}.

Lemma g_left_id_uniq (x:T) : (forall y, g_plus x y = y) -> x = g_zero.
  apply left_id_uniq.
Qed.

Lemma g_left_id_uniq2 (x:T) : (forall y, g_plus x y = y) -> x = g_zero.
  intros left_id.
  rewrite <- (left_id g_zero).
  rewrite (Monoid.m_zero_right x).
  reflexivity.
Qed.

Lemma left_inv_uniq (x x_inv:T) :
  g_plus x_inv x = g_zero -> x_inv = g_inv x.
  intro left_inv.
  rewrite <- (Monoid.m_zero_right x_inv).
  rewrite <- (g_inv_right (Group:=H) x).
  rewrite Monoid.m_plus_assoc.
  rewrite left_inv.
  rewrite Monoid.m_zero_left.
  reflexivity.
Qed.

End Group_Thms.


(***
 *** Fin. (For now...)
 ***)



Spec NatMonoid.

Definition T : Type := nat.
Spec Definition m_zero : T := 0.
Spec Definition m_plus : (T -> T -> T) := plus.

Spec End NatMonoid.

Print NatMonoid.NatMonoid.
Print NatMonoid.NatMonoid__Spec.


Spec Interpretation monoid_natmonoid : Monoid -> NatMonoid := { T +-> nat }.
Next Obligation.
  constructor.
  apply plus_0_l.
  apply plus_0_r.
  apply plus_assoc.
Qed.
Print monoid_natmonoid__instance.

Section NatMonoid_Thms.
Import NatMonoid.
Context `{NatMonoid}.

Lemma nm_left_id_uniq (x:T) : (forall y, m_plus x y = y) -> x = m_zero.
  apply left_id_uniq.
Qed.

End NatMonoid_Thms.


Spec NatMonoid2 := transform NatMonoid.
  start_refinement.
  Unshelve. shelve.
  Focus 2.
  replace 0 with (1 - 1).
  Focus 2. reflexivity.
  Unfocus.
  instantiate (Goal0:=?[m_zero__proof__field]).
  Show Existentials.
  Unshelve.
  Focus 3.
  instantiate_spec ?__Spec.
Defined.

Print NatMonoid2.NatMonoid2.
Print NatMonoid2__refinement.
Print NatMonoid2__instance.

Section NatMonoid2_Thms.
Import NatMonoid2.
Context `{NatMonoid2}.

Lemma nm2_left_id_uniq x : (forall y, m_plus__field x y = y) -> x = m_zero__field.
  apply left_id_uniq.
Qed.

End NatMonoid2_Thms.


Spec Group2.

Spec Variable T : Type.
Spec Variable g_zero : T.
Spec Variable g_plus : (T -> T -> T).

Spec Variable g_inv : (T -> T).

Spec Axiom g_zero_left : (forall x, g_plus g_zero x = x).
Spec Axiom g_zero_right : (forall x, g_plus x g_zero = x).
Spec Axiom g_plus_assoc : (forall x y z, g_plus x (g_plus y z) = g_plus (g_plus x y) z).

Spec Axiom g_inv_left : (forall (x:T), g_plus (g_inv x) x = g_zero).
Spec Axiom g_inv_right : (forall (x:T), g_plus x (g_inv x) = g_zero).

Spec End Group2.


Spec Interpretation Monoid_Group2 : Monoid -> Group2 := { m_% +-> g_% }.
Next Obligation.
destruct Group2__proofs; constructor; assumption.
Defined.

Print Monoid_Group2__instance.

Section Group2_Thms.
Import Group2.
Context `{Group2}.

Lemma g2_left_id_uniq (x:T) : (forall y, g_plus x y = y) -> x = g_zero.
  apply left_id_uniq.
Qed.

End Group2_Thms.





Spec Group3 := Monoid[Monoid_Group2 { T +-> T } ].

Section Group3_Thms.
Import Group3.
Context `{Group3}.
Lemma g3_left_id_uniq (x:T) : (forall y, g_plus x y = y) -> x = g_zero.
  apply left_id_uniq.
Qed.
End Group3_Thms.



(* FIXME: do the Monoid -> NatMonoid interpretation *)


(* FIXME: allow imports to shadow existing ops and axioms *)

Spec MonoidImport1.

Spec Variable T : Type.
Spec Variable m1_plus : (T -> T -> T).
Spec Axiom m1_plus_assoc : (forall x y z, m1_plus x (m1_plus y z) = m1_plus (m1_plus x y) z).

Spec Import Monoid {m_% +-> m1_%}.

Spec End MonoidImport1.


(* FIXME: allow imports to share an op (should be the same as shadowing...) *)

Spec DoubleMonoid.

Spec Import Monoid {m_% +-> m1_%}.
Spec Import Monoid {m_% +-> m2_%}.

Spec End DoubleMonoid.

Print DoubleMonoid.
