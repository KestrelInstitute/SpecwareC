
Declare ML Module "specware".

Spec S1 {
       Variable x : nat
     }.

Print S1.

Spec S2 {
       Variable x : nat ;
       Axiom x_gt_5 : (x > 5)
     }.
Print S2.

Spec S3 {
       Variable x : nat ;
       Definition y : nat := (x + 2)
     }.
Print S3.

(*
Definition S3 `{S3.S3} := S3.S3.
Print S3.
*)

(*
Notation S3 := S3.S3.
*)

Class S3 `{S3.S3} := { }.

Definition z `{S3} := S3.y + 5.
Print z.
Eval compute in z (x__param := 2).

Export S3.

Definition z2 `{S3} := y + 5.
Print z2.
Eval compute in z2 (x__param := 3).


Spec blah {
       Variable x : nat;
       Definition y := 5
     }.