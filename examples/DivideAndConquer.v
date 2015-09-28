
Add LoadPath "../theories" as Specware.
Require Export Specware.SpecwareC.

(* Required for the "Function" mechanism used below *)
Require Import Recdef.
Require Import Coq.Program.Wf.


(***
 *** The Problem Spec
 ***)

(* The problem spec contains the variable to be solved by divide-and-conquer
along with its types and correctness specification *)
Spec DivideAndConquer_problem.

(* Domain and range types *)
Spec Variable D : Type.
Spec Variable R : Type.

(* Input / output predicates *)
Spec Variable IO : (D -> R -> Prop).

(* The function itself *)
Spec Variable solve : (D -> R).
Spec Axiom solve_correct : (forall d, IO d (solve d)).

Spec End DivideAndConquer_problem.


(***
 *** The Solution Spec
 ***)

(* The solution spec, with the sub-components needed to solve the problem *)
Spec DivideAndConquer_soln.

(* Domain and range types *)
Spec Variable D : Type.
Spec Variable R : Type.

(* Input / output predicates *)
Spec Variable IO : (D -> R -> Prop).

(* The well-founded partial order on the inputs *)
Spec Variable smaller : (D -> D -> Prop) | (well_founded smaller).

(* The helper operations *)
Spec Variable primitive : (D -> bool).
Spec Variable direct_solve : (D -> R).
Spec Variable decompose : (D -> D * D) | (forall d,
                                            primitive d = false ->
                                            smaller (fst (decompose d)) d /\
                                            smaller (snd (decompose d)) d).
Spec Variable compose : (R -> R -> R).


(* Soundness axioms *)
Spec Axiom direct_solve_correct :
  (forall d, primitive d = true -> IO d (direct_solve d)).
Spec Axiom solve_soundness :
  (forall d z1 z2,
     IO (fst (decompose d)) z1 ->
     IO (snd (decompose d)) z2 ->
     IO d (compose z1 z2)).

Spec End DivideAndConquer_soln.


(***
 *** Definition of the Solver
 ***)

Section Solver.
Import DivideAndConquer_soln.
Context `{DivideAndConquer_soln}.

(* The solver *)
Function solve_def (d:D) {wf smaller d} : R :=
  if primitive d then
    direct_solve d
  else
    let (d1, d2) := decompose d in
    compose (solve_def d1) (solve_def d2).
intros.
replace d2 with (snd (decompose d)); [ | rewrite teq0; reflexivity ].
apply (proj2 (decompose__proof _ teq)).
intros.
replace d1 with (fst (decompose d)); [ | rewrite teq0; reflexivity ].
apply (proj1 (decompose__proof _ teq)).
assumption.
Defined.

Theorem solve_correct : (forall d, IO d (solve_def d)).
intros.
functional induction (solve_def d).
apply direct_solve_correct; assumption.
apply solve_soundness.
rewrite e0; apply IHr.
rewrite e0; apply IHr0.
Qed.

End Solver.


(***
 *** Interpretation from problem spec to solution spec
 ***)

Spec Interpretation DnC_interp : DivideAndConquer_problem -> DivideAndConquer_soln :=
  { solve +-> (solve_def (smaller__proof:=smaller__proof) (primitive:=primitive)
                         (direct_solve:=direct_solve) (decompose__proof:=decompose__proof)
                         (compose:=compose)) }.
Next Obligation.
constructor.
apply solve_correct.
Defined.
