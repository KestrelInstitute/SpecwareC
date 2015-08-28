(* Re-doing Examples/Specware-Overview/MergeSort.sw in SpecwareCoq *)

Load DivideAndConquer.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Div2.

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


Spec MergeSort0.

(* Domain and range types *)
Spec Definition D : Type := (list nat).
Spec Definition R : Type := (list nat).

(* Input / output predicate *)
Spec Definition IO : (D -> R -> Prop) :=
  (fun lin lout => sorted lout /\ permOf lin lout).

(* The well-founded partial order on the inputs *)
Spec Definition smaller : (D -> D -> Prop) :=
  (fun l1 l2 => length l1 < length l2).

(* The helper operations *)
Spec Definition primitive : (D -> bool) :=
  (fun l => if Coq.Arith.Compare_dec.lt_dec (length l) 2 then true else false).

(* Split l into (l1,l2) where l1 has length n *)
Program Fixpoint list_split n (l : {l:list nat | n <= length l}) : list nat * list nat :=
  match n with
    | 0 => ([], l)
    | S n' =>
      match l with
        | [] => match (_:False) with end
        | x::l' =>
          let (l1,l2) := list_split n' l' in (x::l1, l2)
      end
  end.
Next Obligation.
apply (le_Sn_0 _ H).
Defined.
Next Obligation.
apply le_S_n; assumption.
Defined.

Theorem list_split_app n l l_pf :
  fst (list_split n (exist _ l l_pf)) ++ snd (list_split n (exist _ l l_pf)) = l.
  transitivity (let (l1,l2) := list_split n (exist _ l l_pf) in l1 ++ l2).
  destruct (list_split
              n
              (exist (fun l0 : list nat => n <= Datatypes.length l0) l l_pf));
    reflexivity.
  revert l l_pf; induction n; intros.
  unfold list_split; reflexivity.
  destruct l.
  elimtype False; apply (le_Sn_0 _ l_pf).
  unfold list_split; fold list_split; unfold proj1_sig.
  replace (n0 :: l) with
  (n0::(let (l1,l2) :=
            (list_split
               n
               (exist
                  _ l
                  (list_split_obligation_2
                        (S n)
                        (exist (fun l0 : list nat => S n <= Datatypes.length l0)
                               (n0 :: l) l_pf) n eq_refl n0 l eq_refl)))
        in (l1 ++ l2))).
  destruct (list_split n
                       (exist (fun l0 : list nat => n <= Datatypes.length l0) l
                              (list_split_obligation_2 (S n)
                                                       (exist (fun l0 : list nat => S n <= Datatypes.length l0)
                                                              (n0 :: l) l_pf) n eq_refl n0 l eq_refl))).
  reflexivity.
  f_equal.
  rewrite IHn.
  reflexivity.
Qed.

Program Definition list_split_len l : list nat * list nat :=
  list_split (div2 (length l)) l.
Next Obligation.
admit. (* FIXME: prove this! *)
Defined.

Spec Definition decompose : (D -> D * D) := list_split_len.

Definition list_pair_smaller (l_pair1: list nat * list nat)
           (l_pair2: list nat * list nat) : Prop :=
  length (fst l_pair1) + length (snd l_pair1)
  <
  length (fst l_pair2) + length (snd l_pair2).

Theorem list_pair_smaller_wf : well_founded list_pair_smaller.

Function merge_lists (l_pair: ) : 

Spec Definition compose : (R -> R -> R) :=
  

Spec Variable direct_solve : (D -> R).

(* Soundness axioms *)
Spec Axiom direct_solve_correct :
  (forall d, primitive d = true -> IO d (direct_solve d)).
Spec Axiom solve_soundness :
  (forall d z1 z2,
     IO (fst (decompose d)) z1 ->
     IO (snd (decompose d)) z2 ->
     IO d (compose z1 z2)).
