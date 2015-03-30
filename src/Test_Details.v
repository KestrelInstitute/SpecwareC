
Class T__c : Type := T : Set.
Class m_zero__c {T__p:T__c} : Type := m_zero : T.
Class m_plus__c {T__p:T__c} {m_zero__p:m_zero__c} : Type := m_plus : T -> T -> T.

Class m_zero_left__c {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} : Prop :=
  m_zero_left : forall x, m_plus m_zero x = x.

Class m_zero_right__c {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} : Prop :=
  m_zero_right : forall x, m_plus x m_zero = x.

Class m_plus_assoc__c {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} : Prop :=
  m_plus_assoc : forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z.

Class Monoid {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c}
      {m_zero_left__p:m_zero_left__c} {m_zero_right__p:m_zero_right__c}
      {m_plus_assoc__p:m_plus_assoc__c}
: Prop :=
  { }.

Lemma left_id_uniq `{Monoid} (x:T) :
  (forall y, m_plus x y = y) -> x = m_zero.
  intros left_id.
  rewrite <- (left_id m_zero).
  rewrite m_zero_right.
  reflexivity.
Qed.

Require Import Coq.Arith.Plus.

(* FIXME HERE: how to start building an instance of Monoid without
   already having all the proofs? *)
Require Import Coq.Program.Tactics.
Program Definition m_nat_inst__def :
  Monoid (T__p:=nat) (m_zero__p:=O) (m_plus__p:=plus)
         (m_zero_left__p:=_) (m_zero_right__p:=_) (m_plus_assoc__p:=_) := Build_Monoid _ _ _ _ _ _.
Obligation 1.
constructor.
Qed.
Obligation 2.
unfold m_zero_right__c; intro; rewrite <- plus_n_O; reflexivity.
Qed.
Obligation 3.
unfold m_plus_assoc__c; intros. rewrite plus_assoc; reflexivity.
Qed.

Instance m_nat_inst : Monoid (T__p:=nat) (m_zero__p:=O) (m_plus__p:=plus)
                             (m_zero_left__p:=_) (m_zero_right__p:=_) (m_plus_assoc__p:=_) := m_nat_inst__def.


(* Old way of doing things: no classes for axioms *)

Class T__c : Type := T : Set.
Class m_zero__c {T__p:T__c} : Type := m_zero : T.
Class m_plus__c {T__p:T__c} {m_zero__p:m_zero__c} : Type := m_plus : T -> T -> T.

Class Monoid {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} : Prop :=
  { m_zero_left :> m_zero_left__c;
    m_zero_right :> m_zero_right__c;
    m_plus_assoc : m_plus_assoc__c }.

Lemma left_id_uniq `{Monoid} (x:T) :
  (forall y, m_plus x y = y) -> x = m_zero.
  intros left_id.
  rewrite <- (left_id m_zero).
  rewrite m_zero_right.
  reflexivity.
Qed.

Class U__c : Type := U : Set.
Instance T__inst {U__p:U__c} : T__c := U__p.

Eval unfold T__inst,m_zero__c,T in (forall {U__p:U__c}, m_zero__c (T__p:=T__inst)).
(*
Definition g_zero__t := Eval unfold T__inst,m_zero__c,T in (forall {U__p:U__c}, m_zero__c (T__p:=T__inst)).
*)
(*
Definition g_zero__t {U__p:U__c} : Type := $( apply m_zero__c; unfold m_zero__c )$.
*)
(*
Definition g_zero__t {U__p:U__c} := Eval fold (@U U__p) in U__p.
*)
(* Print g_zero__t. *)

Section blah.
Context {U__p:U__c}.
Definition g_zero__t := Eval fold U in U__p.
End blah.
Print g_zero__t.

Eval unfold m_zero__c,T,T__inst in (forall {U__p:U__c}, m_zero__c (T__p:=T__inst)).


Typeclasses Transparent T__inst.
Class g_zero__c {U__p:U__c} : Type := g_zero : T.
Instance m_zero__inst {U__p:U__c} {g_zero__p:g_zero__c} : m_zero__c (T__p:=T__inst) := g_zero__p.
Typeclasses Transparent m_zero__inst.
Class g_plus__c {U__p:U__c} {g_zero__p:g_zero__c} : Type := g_plus : T -> T -> T.
Instance m_plus__inst {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} :
  m_plus__c (T__p:=T__inst) (m_zero__p:=m_zero__inst) := g_plus__p.
Typeclasses Transparent m_plus__inst.
Class g_inv__c {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} : Type := g_inv : T -> T.

Class Group {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} {g_inv__p:g_inv__c} : Prop :=
  { g_zero_left : forall x, g_plus g_zero x = x;
    g_zero_right : forall x, g_plus x g_zero = x;
    g_plus_assoc : forall x y z, g_plus x (g_plus y z) = g_plus (g_plus x y) z;
    g_inv_left : forall x, g_plus (g_inv x) x = g_zero;
    g_inv_right : forall x, g_plus x (g_inv x) = g_zero }.

Instance Group_Monoid `{Group} : Monoid (T__p:=T__inst) (m_zero__p:=m_zero__inst) (m_plus__p:=m_plus__inst) :=
  {| m_zero_left := g_zero_left;
     m_zero_right := g_zero_right;
     m_plus_assoc := g_plus_assoc |}.

Lemma left_inv_uniq `{Group} (x x_inv:T) :
  g_plus x_inv x = g_zero -> x_inv = g_inv x.
  intro left_inv.
  rewrite <- (g_zero_right x_inv).
  Check g_inv_right.
  rewrite <- (g_inv_right x).
  rewrite g_plus_assoc.
  rewrite left_inv.
  rewrite g_zero_left.
  reflexivity.
Qed.

Lemma g_left_id_uniq `{Group} (x:T) : (forall y, g_plus x y = y) -> x = g_zero.
  apply left_id_uniq.
Qed.





(* FIXME: old versions below *)

Definition T__t : Type := Set.
Class T__c : Type := T : T__t.
Definition m_zero__t {T__p:T__c} : Type := T.
Class m_zero__c {T__p:T__c} : Type := m_zero : m_zero__t.
Definition m_plus__t {T__p:T__c} {m_zero__p:m_zero__c} : Type := T -> T -> T.
Class m_plus__c {T__p:T__c} {m_zero__p:m_zero__c} : Type := m_plus : m_plus__t.

Definition m_zero_left__type {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} := forall x, m_plus m_zero x = x.
Definition m_zero_right {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} := (forall x, m_plus x m_zero = x).
Definition m_plus_assoc {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} := (forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z).

Set Printing All.
Check m_zero_left__type.

Class Monoid {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} : Prop :=
  { m_zero_left : forall x, m_plus m_zero x = x;
    m_zero_right : forall x, m_plus x m_zero = x;
    m_plus_assoc : forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z }.

Check m_zero_left.

Definition m_plus_inv {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} : Prop :=
  forall x, m_plus x x = m_zero.

Class U__c : Type := U : T__t.
Instance T__inst {U__p:U__c} : T__c := U__p.
Class g_zero__c {U__p:U__c} : Type := g_zero : m_zero__t (T__p:=T__inst).
Instance m_zero__inst {U__p:U__c} {g_zero__p:g_zero__c} : m_zero__c (T__p:=T__inst) := g_zero__p.
Class g_plus__c {U__p:U__c} {g_zero__p:g_zero__c} : Type := g_plus : m_plus__t (T__p:=T__inst) (m_zero__p:=m_zero__inst).
Instance m_plus__inst {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} :
  m_plus__c (T__p:=T__inst) (m_zero__p:=m_zero__inst) := g_plus__p.

Set Printing All.

Definition g_plus_inv {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} : Prop :=
  forall x, g_plus x x = g_zero.



Definition T__t : Type := Set.
Class T__c : Type := T : T__t.
Definition m_zero__t {T__p:T__c} : Type := T.
Class m_zero__c {T__p:T__c} : Type := m_zero : m_zero__t.
Definition m_plus__t {T__p:T__c} {m_zero__p:m_zero__c} : Type := T -> T -> T.
Class m_plus__c {T__p:T__c} {m_zero__p:m_zero__c} : Type := m_plus : m_plus__t.

Definition m_plus_inv {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} : Prop :=
  forall x, m_plus x x = m_zero.

Class U__c : Type := U : T__t.
Instance T__inst {U__p:U__c} : T__c := U__p.
Class g_zero__c {U__p:U__c} : Type := g_zero : m_zero__t (T__p:=T__inst).
Instance m_zero__inst {U__p:U__c} {g_zero__p:g_zero__c} : m_zero__c (T__p:=T__inst) := g_zero__p.
Class g_plus__c {U__p:U__c} {g_zero__p:g_zero__c} : Type := g_plus : m_plus__t (T__p:=T__inst) (m_zero__p:=m_zero__inst).
Instance m_plus__inst {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} :
  m_plus__c (T__p:=T__inst) (m_zero__p:=m_zero__inst) := g_plus__p.

Set Printing All.

Definition g_plus_inv {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} : Prop :=
  forall x, g_plus x x = g_zero.



(* FIXME HERE: this does not work! (g_plus_inv fails below) *)
(*
Class T__c : Type := T : Set.
Class m_zero__c {T__p:T__c} : Type := m_zero : T.
Class m_plus__c {T__p:T__c} {m_zero__p:m_zero__c} : Type := m_plus : T -> T -> T.

Definition m_plus_inv {T__p:T__c} {m_zero__p:m_zero__c} {m_plus__p:m_plus__c} : Prop :=
  forall x, m_plus x x = m_zero.

Class U__c : Type := U : T__c.
(*Instance T__inst {U__p:U__c} : T__c := U__p.*)
Class g_zero__c {U__p:U__c} : Type := g_zero : m_zero__c (T__p:=U__p).
(* Instance m_zero__inst {U__p:U__c} {g_zero__p:g_zero__c} : m_zero__c (T__p:=U__p) := g_zero__p. *)
Class g_plus__c {U__p:U__c} {g_zero__p:g_zero__c} : Type := g_plus : m_plus__c (T__p:=U__p) (m_zero__p:=g_zero__p).
(*
Instance m_plus__inst {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} :
  m_plus__c (T__p:=T__inst) (m_zero__p:=m_zero__inst) := g_plus__p.
*)

Set Printing All.

Definition g_plus_inv {U__p:U__c} {g_zero__p:g_zero__c} {g_plus__p:g_plus__c} : Prop :=
  forall x, g_plus x x = g_zero.
*)



