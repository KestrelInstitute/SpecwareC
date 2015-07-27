
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

Print Monoid.Monoid__repr.

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


(* The version of Group that works right now... *)
Spec GroupTest.

Spec ImportTerm (id_refinement_import _ _ Monoid.Monoid__iso).

Spec Variable m_inv : (T -> T).
Spec Axiom m_inv_left : (forall (x:T), m_plus (m_inv x) x = m_zero).
Spec Axiom m_inv_right : (forall (x:T), m_plus x (m_inv x) = m_zero).

(*
Check (toIsoInterp
         (iso1:=Monoid.Monoid__iso)
         (iso2:=Monoid.Monoid__iso)
         spec_instance__0 T__param m_zero__param m_plus__param
         {| Monoid.m_zero_left__axiom := m_zero_left;
            Monoid.m_zero_right__axiom := m_zero_right;
            Monoid.m_plus_assoc__axiom := m_plus_assoc |}
).
*)

Spec End GroupTest.



Class mon_ops : Type :=
  mon_spec_ops : spec_ops Monoid.Monoid__repr.
Class mon_model {ops:mon_ops} : Prop :=
  mon_spec_model : spec_model Monoid.Monoid__repr mon_spec_ops.

Instance mon_T__instance `{mon_ops} : Monoid.T__class :=
  ops_head mon_spec_ops.
Instance mon_m_zero__instance `{mon_ops} : Monoid.m_zero__class :=
  ops_head (ops_rest mon_spec_ops).
Instance mon_m_plus__instance `{mon_ops} : Monoid.m_plus__class :=
  ops_head (ops_rest (ops_rest mon_spec_ops)).

Instance mon__instance `{mon_model} : Monoid.Monoid.
revert ops H.
unfold mon_ops; unfold mon_model; unfold Monoid.Monoid__repr.
intro ops.
repeat (let t := fresh "t" in
        let pf := fresh "pf" in
        destruct ops as [t ops]; destruct ops as [pf ops];
        try destruct pf).
compute.
intro H; repeat (let Hi := fresh "H" in
                 destruct H as [Hi H]); constructor; assumption.
Qed.


Definition grp_repr__ops `{GroupTest.GroupTest} : spec_ops GroupTest.GroupTest__repr :=
  ops_cons
    T__param (I : sats_op_pred None _)
    (ops_cons
       m_zero__param (I : sats_op_pred None _)
       (ops_cons
          m_plus__param (I : sats_op_pred None _)
          (ops_cons
             m_inv__param (I : sats_op_pred None _)
             (tt : spec_ops (Spec_Axioms _))))).

Definition grp_repr__model `{GroupTest.GroupTest} :
  spec_model GroupTest.GroupTest__repr grp_repr__ops.
  compute.
  destruct H.
  repeat (first [ assumption | split; [assumption|] | apply I]).
Qed.

Definition mon_group_interp :
  Interpretation Monoid.Monoid__repr GroupTest.GroupTest__repr :=
  ref_import_interp
    _ (nth_refinement_import
         (refinement_interp GroupTest.spec__import0
                            (@sub_spec_interp
                               Monoid.Monoid__repr GroupTest.GroupTest__repr
                               $(prove_sub_spec)$
         )) 0 $(auto)$).

(*
Instance group_mon_ops__instance `{GroupTest.GroupTest} : mon_ops :=
  map_ops mon_group_interp grp_repr__ops.
Instance group_mon_model__instance `{GroupTest.GroupTest} : mon_model :=
  map_model mon_group_interp _ grp_repr__model.
*)

Section test.

Context `{GroupTest.GroupTest}.

Eval compute in (@mon_T__instance (map_ops mon_group_interp grp_repr__ops)).
Instance grp_mon_T_inst : Monoid.T__class := T__param.

Eval compute in (@mon_m_zero__instance (map_ops mon_group_interp grp_repr__ops)).
Instance grp_mon_m_zero_inst : @Monoid.m_zero__class T__param := m_zero__param.

Eval compute in (@mon_m_plus__instance (map_ops mon_group_interp grp_repr__ops)).
Instance grp_mon_m_plus_inst : @Monoid.m_plus__class T__param := m_plus__param.

Instance grp_mon_inst : @Monoid.Monoid T__param m_zero__param m_plus__param :=
  @mon__instance _ (map_model mon_group_interp _ grp_repr__model).

End test.

(*
Definition import_0_0__isoInterp :
  IsoInterpretation Monoid.Monoid__iso GroupTest.GroupTest__iso (proj1_sig mon_group_interp) :=
  toIsoInterp mon_group_interp.
*)

(*
Instance import_0_0_instance__T `{GroupTest.GroupTest}

Instance group_mon_T `{T__param:GroupTest.T__class} : Monoid.T__class := T__param.
Instance group_mon_m_zero `{m_zero__param:GroupTest.m_zero__class} :
  Monoid.m_zero__class := m_zero__param.
Instance group_mon_m_plus `{m_plus__param:GroupTest.m_plus__class} :
  Monoid.m_plus__class := m_plus__param.

Instance test_inst1 {T__param m_zero__param m_plus__param m_inv__param}
         {s: @GroupTest.GroupTest T__param m_zero__param
                                     m_plus__param m_inv__param} :
  Monoid.Monoid :=
  (toIsoInterp
     (iso1:=Monoid.Monoid__iso)
     (iso2:=Monoid.Monoid__iso)
     GroupTest.spec_instance__0 T__param m_zero__param m_plus__param
     {| Monoid.m_zero_left__axiom := GroupTest.m_zero_left__axiom (GroupTest:=s);
        Monoid.m_zero_right__axiom := GroupTest.m_zero_right__axiom (GroupTest:=s);
        Monoid.m_plus_assoc__axiom := GroupTest.m_plus_assoc__axiom (GroupTest:=s) |}
  ).
Check @test_inst1.

Set Printing All.

Check @GroupTest.m_zero_right__axiom.
*)


Section GroupTest_Thms.
Import GroupTest.
Context `{GroupTest}.

(*
Hint Extern 5 (@Monoid.Monoid _ _ _) =>
     (unfold mon_T__instance; unfold mon_m_zero__instance; unfold mon_m_plus__instance;
      unfold group_mon_ops__instance) : typeclass_instances.
*)

Definition blah := left_id_uniq.
Set Printing All.
Check blah.

Lemma m_left_id_uniq (x:T) : (forall y, m_plus x y = y) -> x = m_zero.
  apply left_id_uniq.
Qed.

Lemma m_left_id_uniq2 (x:T) : (forall y, m_plus x y = y) -> x = m_zero.
  intros left_id.
  rewrite <- (left_id m_zero).
  rewrite m_zero_right.
  reflexivity.
Qed.

(*
Instance m_zero_right__inst : m_zero_right__class :=
  m_zero_right__axiom (GroupTest:=H).
*)

Lemma left_inv_uniq (x x_inv:T) :
  m_plus x_inv x = m_zero -> x_inv = m_inv x.
  intro left_inv.
  (* FIXME: can we get rid of the T__param argument here? *)
  rewrite <- (m_zero_right (T__param:=T__param) x_inv).
  rewrite <- (m_inv_right x).
  rewrite m_plus_assoc.
  rewrite left_inv.
  rewrite m_zero_left.
  reflexivity.
Qed.

End GroupTest_Thms.



(* The "correct" version of Group *)
Spec Group.

Spec Import Monoid {m_% +-> g_%}.

Spec Variable g_inv : (T -> T).
Spec Axiom g_inv_left : (forall (x:T), g_plus (g_inv x) x = g_zero).
Spec Axiom g_inv_right : (forall (x:T), g_plus x (g_inv x) = g_zero).

Spec End Group.

Print Group.

Section Group_Thms.
Import Group.
Context `{Group}.

Lemma g_left_id_uniq (x:T) : (forall y, g_plus x y = y) -> x = g_zero.
  apply left_id_uniq.
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
