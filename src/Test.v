
Declare ML Module "specware".

Spec S1 {
       Variable x : nat
     }.

Print S1.

Spec S2 {
       Variable x2 : nat ;
       Axiom x_gt_5 : (x2 > 5)
     }.
Print S2.

Spec S3 {
       Variable x3 : nat ;
       Definition y : nat := (x3 + 2)
     }.
Print S3.
Print x3__class.

Definition z `{S3} := y + 5.
Print z.
Eval compute in z (x3__param := 2).

Spec blah {
       Variable x : nat;
       Definition y := 5
     }.