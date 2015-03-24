
Declare ML Module "specware".

Spec Monoid.

Spec Variable T : Type.
(*
Hint Extern 0 T__class => assumption : typeclass_instances.
Hint Extern 0 T__type => fold T__class; assumption : typeclass_instances.
Typeclasses Opaque T__class T__type T.
*)
(*
Spec Definition id_T : (T -> T) := (fun x => x).
Hint Extern 0 id_T__class => assumption.
Typeclasses Opaque id_T__class id_T__type id_T.
*)
Spec Variable m_zero : T.
(*
Hint Extern 0 m_zero__class => assumption : typeclass_instances.
Typeclasses Opaque m_zero__class m_zero__type m_zero.
*)
Spec Variable m_plus : (T -> T -> T).
(*
Hint Extern 0 m_plus__class => assumption : typeclass_instances.
Typeclasses Opaque m_plus__class m_plus__type m_plus.
*)
Set Printing All.
Print m_plus__type.

Spec Axiom m_zero_left : (forall x, m_plus m_zero x = x).
Print m_zero_left__type. Print m_zero__type.
Spec Axiom m_zero_right : (forall x, m_plus x m_zero = x).
Spec Axiom m_plus_assoc : (forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z).

Spec End Monoid.

Module Monoid_Thms.
Import Monoid.
Lemma left_id_uniq `{Monoid} (x:T) :
  (forall y, m_plus x y = y) -> x = m_zero.
  intros left_id.
  rewrite <- (left_id m_zero).
  Set Printing All.
  Print m_zero__type. Print Monoid.
  Eval compute in m_zero_right__type.
  Eval compute in (@T T__param).
  unfold T. unfold m_plus. unfold m_zero.
  rewrite (m_zero_right H).

End Monoid_Thms.

Print Monoid.
Set Printing All.
Print Monoid.m_zero_left__type.
Print Monoid.m_zero__type.
Print Monoid.m_zero.
Print Monoid.m_plus__type.

Check (forall `{Monoid.m_plus__class} (x:@Monoid.T T__param), Monoid.m_plus Monoid.m_zero x = x).

(* FIXME: get undo to work! *)
Spec Group.

Set Printing All.

Spec Import Monoid {m_% +-> g_%}.
Spec Variable g_inv : (T -> T).
Spec Axiom g_inv_left : (forall (x:T), g_plus (g_inv x) x = g_zero).
Spec Axiom g_inv_right : (forall (x:T), g_plus x (g_inv x) = g_zero).

Spec End Group.

Print Group.


Lemma `{Group.Group} 


Print Monoid.
Class foo `{S1.S1} : Type := { }.
Set Printing All.
Print foo. Check Build_foo.
Instance T__param_nat : S1.T__class := nat.
Print T__param_nat.
Class foo2 `{foo (T__param:=T__param_nat)} : Type := { my_x := S1.x }.
Print foo2.

(*
Definition x'__class := S1.x__class.
Print x'__class.
*)
Class x'__class {T__param : S1.T__class} : Type := x' : S1.x__class.
Class y'__class {T__param : S1.T__class} {x'__param : x'__class} := y' : S1.y__class (x__param:=x'__param).
Class foo3 {x'__param : x'__class} {y'__param : y'__class} `{foo (x__param:=x'__param) (y__param:=y'__param)} : Type := { }.
Print x'__class.
Print foo3.

Print S1.
Print S1.id_T.

Spec S2 {
       Variable x : nat ;
       Variable y : nat ;
       Axiom x_gt_5 : (x > 5) ;
       Axiom x_lt_y : (x < y)
     }.
Print S2.
Print S2.x.

Spec S3 {
       Variable x : nat ;
       Definition y : nat := (x + 2) ;
       Definition foo : (nat -> nat) := (fun z => z + y)
     }.
Check S3.foo.
Print S3.
Print S3.y.

(*
Class Foo {baz : S1.T__class} : Type := x : x'__class (T__param := baz).
*)

Spec S4 {
       Variable x : nat ;
       Import S3
     }.

(*
Definition S3 `{S3.S3} := S3.S3.
Print S3.
*)

(*
Notation S3 := S3.S3.
*)

(*
Class S3 `{S3.S3} := { }.

Definition z `{S3} := S3.y + 5.
Print z.
Eval compute in z (x__param := 2).
*)

(* Export S3. *)
Import S3.
(* Context `{S3}. *)

Lemma foo_n_gt_y `{S3} : forall n, foo n >= y.
  intro n.
  unfold foo.
  induction n.
  rewrite plus_O_n.
  apply le_n.
  rewrite plus_Sn_m.
  apply le_S.
  assumption.
Qed.

Definition some_gt_y `{S3} : { n : nat | n > y }.
  exists (2 + y).
  unfold plus.
  apply le_S. apply le_n.
Defined.

Print some_gt_y.
Eval compute in (proj1_sig (some_gt_y (x__param := 2))).

Definition y_plus_5 `{S3} := y + 5.
Print y_plus_5.
Eval compute in z2 (x__param := 3).

Spec blah {
       Variable x : nat;
       Definition y := 5
     }.