
Add LoadPath "../theories" as Specware.
Require Import Specware.SpecwareC.

Require Import Recdef.


(***
 *** Binary Divide-and-Conquer Algorithms
 ***)

Spec DivideAndConquer.

(* Domain and range types *)
Spec Variable D : Set.
Spec Variable R : Set.

(* Input and output predicates *)
Spec Variable I : (D -> Prop).
Spec Variable O : (D -> R -> Prop).

(* The well-founded partial order on the inputs *)
Spec Variable leq : (D -> D -> Prop).
Spec Variable leq_wf : (well_founded leq).

(* The helper operations *)
Spec Variable primitive : (D -> bool).
Spec Variable decompose : (D -> D * D).
Spec Variable compose : (R * R -> R).
Spec Variable direct_solve : (D -> R).

(* Soundness axioms *)
Spec Axiom direct_solve_correct :
  (forall d, I d -> primitive d = true -> O d (direct_solve d)).
Spec Axiom decompose_reduces1 :
  (forall d, leq (fst (decompose d)) d).
Spec Axiom decompose_reduces2 :
  (forall d, leq (snd (decompose d)) d).
Spec Axiom solve_soundness :
  (forall d0 z1 z2,
     O (fst (decompose d0)) z1 ->
     O (snd (decompose d0)) z2 ->
     O d0 (compose (pair z1 z2))).

(* The solver *)
Spec Variable solve : (D -> R).
Spec Axiom solve_correct : (forall d, I d -> O d (solve d)).

Spec End DivideAndConquer.


(* The implementation of divide-and-conquer *)
Spec DivideAndConquer_impl.

(* Domain and range types *)
Spec Variable D : Set.
Spec Variable R : Set.

(* Input and output predicates *)
Spec Variable I : (D -> Prop).
Spec Variable O : (D -> R -> Prop).

(* The well-founded partial order on the inputs *)
Spec Variable leq : (D -> D -> Prop).
Spec Variable leq_wf : (well_founded leq).

(* The helper operations *)
Spec Variable primitive : (D -> bool).
Spec Variable decompose : (D -> D * D).
Spec Variable compose : (R * R -> R).
Spec Variable direct_solve : (D -> R).

(* Soundness axioms *)
Spec Axiom direct_solve_correct :
  (forall d, I d -> primitive d = true -> O d (direct_solve d)).
Spec Axiom decompose_reduces1 :
  (forall d, leq (fst (decompose d)) d).
Spec Axiom decompose_reduces2 :
  (forall d, leq (snd (decompose d)) d).
Spec Axiom solve_soundness :
  (forall d0 z1 z2,
     O (fst (decompose d0)) z1 ->
     O (snd (decompose d0)) z2 ->
     O d0 (compose (pair z1 z2))).

(* The solver *)
Function solve_def (d:D) {wf leq d} : R :=
  if primitive d then
    direct_solve d
  else
    let (d1, d2) := decompose d in
    compose (solve_def d1, solve_def d2).

Spec Definition solve : (D -> R) := solve_def.

Spec Axiom solve_correct :
  (forall d, I d -> O d (solve d)).

Spec End DivideAndConquer_impl.
