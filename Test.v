
Require Import Coq.Arith.Plus.

(* The Monoid spec, with a theorem *)
Module Monoid.

Class Monoid :=
  {
    T : Type;
    zero : T;
    add : T -> T -> T;
    add_assoc : forall t1 t2 t3, add t1 (add t2 t3) = add (add t1 t2) t3;
    add_zero_left : forall t, add zero t = t;
    add_zero_right : forall t, add t zero = t
  }.

Lemma add_add_zero `{Monoid} :
  forall t, add t (add t zero) = add t t.
  intro t; rewrite add_zero_right; reflexivity.
Qed.

End Monoid.

(* The name of the spec is exported without the period *)
Notation Monoid := Monoid.Monoid.


(*
Check Monoid.T.
Print Monoid.T.
*)

(* The Group spec *)
Module Group.

Class Group :=
  {
    T : Type;
    zero : T;
    add : T -> T -> T;
    inv : T -> T;
    add_assoc : forall t1 t2 t3, add t1 (add t2 t3) = add (add t1 t2) t3;
    add_zero_left : forall t, add zero t = t;
    add_zero_right : forall t, add t zero = t;
    add_inv_left : forall t, add (inv t) t = zero;
    add_inv_right : forall t, add t (inv t) = zero
  }.

End Group.

Notation Group := Group.Group.


(*
Module Monoid_Group_morph.
Import Monoid.
*)

(* The morphism from Monoid ==> Group *)

(*
Instance Monoid_Group_morph (G: Group) : Monoid :=
  {|
    T := Group.T;
    zero := Group.zero;
    add := Group.add;
    add_assoc := Group.add_assoc;
    add_zero_left := Group.add_zero_left;
    add_zero_right := Group.add_zero_right
  |}.
*)
Instance Monoid_Group_morph (G: Group) : Monoid :=
  {|
    T := Group.T;
    zero := Group.zero;
    add := Group.add
  |}.
apply Group.add_assoc.
apply Group.add_zero_left.
apply Group.add_zero_right.
Defined.
(* README: This needs to be "Defined" not "Qed" so Monoid_Group_morph
   is transparent when we try to use Monoid theorems below *)

Print Monoid_Group_morph.
(* Coercion Monoid_Group_morph : Group >-> Monoid. *)

(*
End Monoid_Group_morph.
*)


(* Moving the add_add_zero theorem along a morphism *)
Definition add_add_zero_group `{Group} :
  forall t, Group.add t (Group.add t Group.zero) = Group.add t t :=
  Monoid.add_add_zero.

(* Another test to move add_add_zero theorem along a morphism *)
(* README: need to apply add_add_zero to an argument when it is used
   in a tactic script, since otherwise the instance resolution does
   not happen *)
Lemma add_add_zero_zero `{Group} :
  forall t, Group.add t (Group.add t (Group.add Group.zero Group.zero)) = Group.add t t.
  intro t. rewrite Group.add_zero_left.
  apply (Monoid.add_add_zero t).
Qed.


(* README: this is an example of building an instance *)
Definition nat_Monoid : Monoid :=
  {| T := nat; zero := 0; add := plus;
     add_assoc := plus_assoc; add_zero_left := plus_0_l;
     add_zero_right := plus_0_r |}.


