
Add LoadPath "../theories" as Specware.
Require Export Specware.SpecwareC.

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
Spec Variable leq : (D -> D -> Prop) | (well_founded leq).

(* The helper operations *)
Spec Variable primitive : (D -> bool).
Spec Variable decompose : (D -> D * D) | (forall d,
                                            primitive d = false ->
                                            leq (fst (decompose d)) d /\
                                            leq (snd (decompose d)) d).
Spec Variable compose : (R * R -> R).
Spec Variable direct_solve : (D -> R).

(* Soundness axioms *)
Spec Axiom direct_solve_correct :
  (forall d, I d -> primitive d = true -> O d (direct_solve d)).
Spec Axiom decompose_correct1 :
  (forall d, I d -> primitive d = false ->
             I (fst (decompose d))).
Spec Axiom decompose_correct2 :
  (forall d, I d -> primitive d = false ->
             I (snd (decompose d))).
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
Spec Variable leq : (D -> D -> Prop) | (well_founded leq).

(* The helper operations *)
Spec Variable primitive : (D -> bool).
Spec Variable decompose : (D -> D * D) | (forall d,
                                            primitive d = false ->
                                            leq (fst (decompose d)) d /\
                                            leq (snd (decompose d)) d).
Spec Variable compose : (R * R -> R).
Spec Variable direct_solve : (D -> R).

(* Soundness axioms *)
Spec Axiom direct_solve_correct :
  (forall d, I d -> primitive d = true -> O d (direct_solve d)).
Spec Axiom decompose_correct1 :
  (forall d, I d -> primitive d = false ->
             I (fst (decompose d))).
Spec Axiom decompose_correct2 :
  (forall d, I d -> primitive d = false ->
             I (snd (decompose d))).
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
intros.
replace d2 with (snd (decompose d)); [ | rewrite teq0; reflexivity ].
apply (proj2 (decompose__proof _ teq)).
intros.
replace d1 with (fst (decompose d)); [ | rewrite teq0; reflexivity ].
apply (proj1 (decompose__proof _ teq)).
assumption.
Defined.

Spec Definition solve : (D -> R) := solve_def.

Spec Theorem solve_correct : (forall d, I d -> O d (solve d)).
unfold solve; unfold def; intros.
functional induction (solve_def d).
apply direct_solve_correct; assumption.
apply solve_soundness.
assert (d1 = fst (decompose d)) as e1; [ rewrite e0; reflexivity | ].
rewrite <- e1. apply IHr. rewrite e1. apply decompose_correct1; assumption.
assert (d2 = snd (decompose d)) as e2; [ rewrite e0; reflexivity | ].
rewrite <- e2. apply IHr0. rewrite e2. apply decompose_correct2; assumption.
Qed.

Spec End DivideAndConquer_impl.

