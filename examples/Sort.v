
Load DivideAndConquer.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.Peano_dec.

Fixpoint sorted (l: list nat) : Prop :=
  match l with
    | [] => True
    | x::l' =>
      (match l' with
         | [] => True
         | y::_ => x <= y /\ sorted l'
       end)
  end.

Definition permOf (l1 l2: list nat) : Prop :=
  forall x, count_occ eq_nat_dec l1 x = count_occ eq_nat_dec l2 x.



Spec Sorting.

Spec Variable sort : (list nat -> list nat).
Spec Axiom sort_correct :
  (forall l, sorted (sort l) /\ permOf l (sort l)).

Spec End Sorting.


Spec Sorting2.

Spec Import Sorting [[ dc_impl ]].



Definition sort_interp :
  Interpretation DivideAndConquer.DivideAndConquer__Spec
                 Sorting.Sorting__Spec.
  
