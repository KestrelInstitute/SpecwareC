(***
 *** Utility functions and lemmas
 ***)

Add LoadPath "." as MetaSlang.

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
