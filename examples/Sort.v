
Load DivideAndConquer.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.Peano_dec.


(***
 *** Helper definitions to define sorting
 ***)

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


(***
 *** Problem spec for sorting
 ***)

Spec Sorting.

Spec Variable sort : (list nat -> list nat).
Spec Axiom sort_correct :
  (forall l, sorted (sort l) /\ permOf l (sort l)).

Spec End Sorting.


(***
 *** Interpretation from divide-and-conquer problem spec to sorting
 ***)

Spec Interpretation sorting_dnc_interp : DivideAndConquer_problem -> Sorting :=
  { solve +-> sort; IO +-> (fun li lo => sorted lo /\ permOf li lo) }.
Next Obligation.
destruct Sorting__proofs; constructor; assumption.
Defined.


Definition sorting_pushout :
  @GMPushout DivideAndConquer_problem.DivideAndConquer_problem__gspec
             Sorting.Sorting__gspec
             DivideAndConquer_soln.DivideAndConquer_soln__gspec
             sorting_dnc_interp DnC_interp.
  pushout_tac.
Defined.

(* Spec Sorting_dnc := pushout sorting_dnc DnC_interp. *)

Spec Sorting_dnc := raw (gmpo_spec _ _ _ _ _ sorting_pushout).

Print Sorting_dnc.Sorting_dnc.
Print Sorting_dnc.Sorting_dnc__Spec.
