
Add LoadPath "../theories" as Specware.
Require Import Specware.Spec.
Add ML Path "../src".
Declare ML Module "util_specware".
Declare ML Module "specware".

Spec Monoid.

Spec Variable T : Type.
Spec Variable m_zero : T.
Spec Variable m_plus : (T -> T -> T).

Spec Axiom m_zero_left : (forall x, m_plus m_zero x = x).
Spec Axiom m_zero_right : (forall x, m_plus x m_zero = x).
Spec Axiom m_plus_assoc : (forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z).

Spec End Monoid.

Print Monoid.Monoid__Spec.

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

Print left_id_uniq.


Spec Group.

Spec ImportTerm
     (refinement_translate
        (id_refinement_import Monoid.Monoid__Spec)
        (cons (XlateWild "m_" "g_") nil)).

Spec Variable g_inv : (T -> T).
Spec Axiom g_inv_left : (forall (x:T), g_plus (g_inv x) x = g_zero).
Spec Axiom g_inv_right : (forall (x:T), g_plus x (g_inv x) = g_zero).

Spec End Group.



Definition mon_repr__ops {T__param:Monoid.T__class}
           {m_zero__param:Monoid.m_zero__class} {m_plus__param:Monoid.m_plus__class} :
  spec_ops Monoid.Monoid__Spec :=
  ops_cons
    T__param (I : sats_op_pred None _)
    (ops_cons
       m_zero__param (I : sats_op_pred None _)
       (ops_cons
          m_plus__param (I : sats_op_pred None _)
          (tt : spec_ops (Spec_Axioms _)))).

Instance Monoid__IsoM {T__param m_zero__param m_plus__param} :
  IsoToSpecModels mon_repr__ops (@Monoid.Monoid T__param m_zero__param m_plus__param).
  compute; split;
  [ intro H; destruct H;
    repeat (first [ assumption | split; [assumption|] | apply I])
  | intro H; repeat (let Hi := fresh "H" in
                     destruct H as [Hi H]); constructor; assumption ].
Qed.


Definition grp_repr__ops {T__param:Group.T__class}
           {g_zero__param:Group.g_zero__class} {g_plus__param:Group.g_plus__class}
           {g_inv__param:Group.g_inv__class} : spec_ops Group.Group__Spec :=
  ops_cons
    T__param (I : sats_op_pred None _)
    (ops_cons
       g_zero__param (I : sats_op_pred None _)
       (ops_cons
          g_plus__param (I : sats_op_pred None _)
          (ops_cons
             g_inv__param (I : sats_op_pred None _)
             (tt : spec_ops (Spec_Axioms _))))).

Instance Group__IsoM {T__param g_zero__param g_plus__param g_inv__param} :
  IsoToSpecModels grp_repr__ops (@Group.Group T__param g_zero__param g_plus__param g_inv__param).
  compute; split;
  [ intro H; destruct H;
    repeat (first [ assumption | split; [assumption|] | apply I])
  | intro H; repeat (let Hi := fresh "H" in
                     destruct H as [Hi H]); constructor; assumption ].
Qed.


Hint Extern 1 Monoid.T__class =>
  refine (_ : Group.T__class) : typeclass_instances.
Hint Extern 1 Monoid.m_zero__class =>
  refine (_ : Group.g_zero__class) : typeclass_instances.
Hint Extern 1 Monoid.m_plus__class =>
  refine (_ : Group.g_plus__class) : typeclass_instances.

Print Group.spec__import0.

(* NOTE: do not use nth_refinement_import in generated code, just destruct the
actual RefinementOf object and its imports *)
Program Definition mon_group_interp :
  Interpretation Monoid.Monoid__Spec Group.Group__Spec :=
  ref_import_interp
    _ (nth_refinement_import
         (refinement_interp Group.spec__import0
                            (@sub_spec_interp
                               _ Group.Group__Spec
                               _ (* $(prove_sub_spec)$ *)
         )) 0 $(auto)$).
Next Obligation.
prove_sub_spec.
Defined.

Print spec_models_iso.

Instance grp_mon__instance {T__param g_zero__param g_plus__param g_inv__param}
         {H:@Group.Group T__param g_zero__param g_plus__param g_inv__param} :
  @Monoid.Monoid T__param g_zero__param g_plus__param :=
  proj2 (spec_models_iso
           (IsoToSpecModels:= @Monoid__IsoM T__param g_zero__param g_plus__param))
        (map_model mon_group_interp grp_repr__ops
                   (proj1 (spec_models_iso (IsoToSpecModels:=Group__IsoM)) H)).

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
  (* FIXME: can we get rid of the T__param argument here? *)
  rewrite <- (g_zero_right (T__param:=T__param) x_inv).
  rewrite <- (g_inv_right x).
  rewrite g_plus_assoc.
  rewrite left_inv.
  rewrite g_zero_left.
  reflexivity.
Qed.

End Group_Thms.



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

(*
Section Group2_Thms.
Import Group2.
Context `{Group2}.

Lemma g2_left_id_uniq (x:T) : (forall y, g_plus x y = y) -> x = g_zero.
  apply left_id_uniq.
Qed.
*)

Spec Morphism Group2_Monoid : Monoid -> Group2 {m_% +-> g_%}.
constructor.
unfold Monoid.m_zero_left__class.
apply Group2.g_zero_left.
unfold Monoid.m_zero_right__class.
apply Group2.g_zero_right.
unfold Monoid.m_plus_assoc__class.
apply Group2.g_plus_assoc.
Qed.

Print Group2_Monoid.

Section Group2_Thms.
Import Group2.
Context `{Group2}.

Lemma g2_left_id_uniq (x:T) : (forall y, g_plus x y = y) -> x = g_zero.
  apply left_id_uniq.
Qed.
End Group2_Thms.

Spec MorphTest.
Spec Import Monoid[Group2_Monoid].
Spec End MorphTest.


Spec NatMonoid.

Spec Definition T : Type := nat.
Spec Definition m_zero : T := 0.
Spec Definition m_plus : (T -> T -> T) := Nat.add.
(* Spec Variable m_plus : (T -> T -> T). *)

Spec Axiom m_zero_left : (forall x, m_plus m_zero x = x).
Spec Axiom m_zero_right : (forall x, m_plus x m_zero = x).
Spec Axiom m_plus_assoc : (forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z).

Spec End NatMonoid.

Print NatMonoid.

Require Import Coq.Arith.Plus.

Spec Morphism NatMonoid_Monoid : Monoid -> NatMonoid.
constructor.
unfold Monoid.m_zero_left__class.
reflexivity.
unfold Monoid.m_zero_right__class.
intros. compute. fold Nat.add. symmetry. apply plus_n_O.
unfold Monoid.m_plus_assoc__class.
intros. compute. fold Nat.add. apply plus_assoc.
Qed.

Set Printing All.
Check NatMonoid_Monoid.

(*
Spec MonoidImport0.

Spec Variable T : nat.

Spec Import Monoid.

Spec End MonoidImport0.
*)

Spec MonoidImport1.

Spec Variable T : Type.
Spec Variable m1_plus : (T -> T -> T).
Spec Axiom m1_plus_assoc : (forall x y z, m1_plus x (m1_plus y z) = m1_plus (m1_plus x y) z).

Spec Import Monoid {m_% +-> m1_%}.

Spec End MonoidImport1.


Spec DoubleMonoid.

Spec Import Monoid {m_% +-> m1_%}.
Spec Import Monoid {m_% +-> m2_%}.

Spec End DoubleMonoid.

Print DoubleMonoid.

(* FIXME: make a more interesting morphism... *)
(* Spec Morphism MG : Monoid -> Group { m_% +-> g_% }. *)

Print Group.g_zero_left__class.
