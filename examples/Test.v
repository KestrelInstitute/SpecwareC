
Add LoadPath "../theories" as Specware.
Require Import Specware.SpecwareC.


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
Print Monoid.Monoid__Iso.


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
Spec Axiom g_inv_left : (forall (x:T), g_plus (g_inv x) x = g_zero).
Spec Axiom g_inv_right : (forall (x:T), g_plus x (g_inv x) = g_zero).

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
  rewrite g_zero_right.
  reflexivity.
Qed.

Lemma left_inv_uniq (x x_inv:T) :
  g_plus x_inv x = g_zero -> x_inv = g_inv x.
  intro left_inv.
  rewrite <- (g_zero_right x_inv).
  rewrite <- (g_inv_right x).
  rewrite g_plus_assoc.
  rewrite left_inv.
  rewrite g_zero_left.
  reflexivity.
Qed.

End Group_Thms.


(***
 *** Fin. (For now...)
 ***)



Spec NatMonoid.

Spec Definition T : Type := nat.
Spec Definition m_zero : T := 0.
Spec Definition m_plus : (T -> T -> T) := plus.

Spec Axiom m_zero_left : (forall x, m_plus m_zero x = x).
Spec Axiom m_zero_right : (forall x, m_plus x m_zero = x).
Spec Axiom m_plus_assoc : (forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z).

Spec End NatMonoid.

Print NatMonoid.NatMonoid.
Print NatMonoid.NatMonoid__Spec.


(* Building the Monoid -> NatMonoid interpretation manually *)
Section monoid_natmonoid__instance_section.
Import NatMonoid.

Instance monoid_natmonoid__instance
         `{Spec:NatMonoid} :
  Monoid.Monoid (T__param:=T:Type)
                (m_zero__param:=m_zero__var)
                (m_plus__param:=m_plus__var).
constructor.
unfold Monoid.m_zero_left__class, Monoid.T, Monoid.m_zero, Monoid.m_plus.
unfold m_zero__var.
(* FIXME: why do we need m_zero__proof__param instead of m_zero__proof here? *)
rewrite m_zero__proof__param. rewrite m_plus__proof.
apply m_zero_left.
unfold Monoid.m_zero_right__class, Monoid.T, Monoid.m_zero, Monoid.m_plus.
unfold m_zero__var.
rewrite m_zero__proof__param. rewrite m_plus__proof.
apply m_zero_right.
unfold Monoid.m_plus_assoc__class, Monoid.T, Monoid.m_zero, Monoid.m_plus.
rewrite m_plus__proof.
apply m_plus_assoc.
Defined.

Definition monoid_natmonoid : Interpretation Monoid.Monoid__Spec NatMonoid.NatMonoid__Spec :=
  mkInterp
    (fun (ops:spec_ops NatMonoid.NatMonoid__Spec) =>
       match ops with
         | existT
             _ T__var
             (existT
                _ T__proof
                (existT
                   _ m_zero__var
                   (existT
                      _ m_zero__proof
                      (existT
                         _ m_plus__var
                         (existT
                            _ m_plus__proof tt))))) =>
           existT
             _ (nat:Type)
             (existT
                _ I
                (existT
                   _ m_zero__var
                   (existT
                      _ I
                      (existT
                         _ m_plus__var
                         (existT
                            _ I tt))))) : spec_ops Monoid.Monoid__Spec
       end)
    (fun (ops:spec_ops NatMonoid.NatMonoid__Spec) model =>
       match ops with
         | existT
             _ T__var
             (existT
                _ T__proof
                (existT
                   _ m_zero__var
                   (existT
                      _ m_zero__proof
                      (existT
                         _ m_plus__var
                         (existT
                            _ m_plus__proof tt))))) =>
           let T := nat in
           let m_zero := 0 in
           let m_plus := plus in
           proj1 (spec_models_iso
                    (IsoToSpecModels:=
                       Monoid.Monoid__Iso (T__param:=T) (m_zero__param:=m_zero__var)
                                          (m_plus__param:=m_plus__var)))
                 (monoid_natmonoid__instance
                    (Spec:=
                       proj2 (spec_models_iso
                                (IsoToSpecModels:=
                                   @NatMonoid.NatMonoid__Iso T__var T__proof m_zero__var m_zero__proof m_plus__var m_plus__proof))
                             model))
       end).

End monoid_natmonoid__instance_section.

(*
Spec Interpretation monoid_natmonoid2 : Monoid -> NatMonoid := { T +-> (T:Type) }.
Obligation 4.
repeat interp_tactic.
destruct ops.
admit.
Defined.
*)

Spec NatMonoid_Import.
Spec Import NatMonoid.
Spec End NatMonoid_Import.

Print NatMonoid_Import.NatMonoid_Import__Spec.
Print NatMonoid.NatMonoid__Spec.

Spec NatMonoid_Import2 := transform NatMonoid.
apply id_refinement.
Defined.

Print NatMonoid_Import2.NatMonoid_Import2.



(* Building the NatMonoid -> NatMonoid_Import interpretation manually *)
Section natmonoid_natmonoid__instance_section.
Import NatMonoid_Import.
Set Printing All.
Program Instance natmonoid_natmonoid__instance
         `{Spec:NatMonoid_Import} :
  NatMonoid.NatMonoid (T__param:=T__var)
                      (m_zero__param:=m_zero__var)
                      (m_plus__param:=m_plus__var).

(*
Instance natmonoid_natmonoid__instance
         `{Spec:NatMonoid_Import} :
  NatMonoid.NatMonoid (T__param:=T__param)
                      (T__proof__param:=T__proof__param)
                      (m_zero__param:=m_zero__param)
                      (m_zero__proof__param:=m_zero__proof__param)
                      (m_plus__param:=m_plus__param)
                      (m_plus__proof__param:=m_plus__proof__param).
*)


Spec Group2.

Spec Variable T : Type.
Spec Variable g_zero : T.
Spec Variable g_plus : (T -> T -> T).

Spec Axiom g_zero_left : (forall x, g_plus g_zero x = x).
Spec Axiom g_zero_right : (forall x, g_plus x g_zero = x).
Spec Axiom g_plus_assoc : (forall x y z, g_plus x (g_plus y z) = g_plus (g_plus x y) z).

Spec Variable g_inv : (T -> T).
Spec Axiom g_inv_left : (forall (x:T), g_plus (g_inv x) x = g_zero).
Spec Axiom g_inv_right : (forall (x:T), g_plus x (g_inv x) = g_zero).

Spec End Group2.


Spec Interpretation Monoid_Group2 : Monoid -> Group2.
unfold Monoid.Monoid__Spec, Group2.Group2__Spec.
apply (interp_cons_strengthen_xlate { "m_"% +-> "g_"% });
  [ intros; apply I | ].
intro_string ("T"%string).

prove_simple_interp { "m_"% +-> "g_"% }.
Defined.


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
