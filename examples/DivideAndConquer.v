
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

(* The helper operations *)
Spec Variable primitive : (D -> bool).
Spec Variable direct_solve : (D -> R).
Spec Variable decomposeL : (D -> D).
Spec Variable decomposeR : (D -> D).
Spec Variable compose : (R -> R -> R).

(* The well-founded partial order on the inputs *)
Spec Variable smaller : (D -> D -> Prop).

(* Axiom: smaller is well-founded *)
Spec Axiom smaller_wf : (well_founded smaller).

(* The decomposition operations must yield smaller inputs *)
Spec Axiom smaller_decomposeL :
  (forall d, primitive d = false -> smaller (decomposeL d) d).
Spec Axiom smaller_decomposeR :
  (forall d, primitive d = false -> smaller (decomposeR d) d).

(* Soundness axioms *)
Spec Axiom direct_solve_correct :
  (forall d, primitive d = true -> IO d (direct_solve d)).
Spec Axiom decompose_compose_correct :
  (forall d rL rR,
     IO (decomposeL d) rL -> IO (decomposeR d) rR -> IO d (compose rL rR)).

(* FIXME: solve_def should really go here; need to hook into Coq's
generalization mechanism so that when the spec ends, solve_def automatically
quantifies over a DivideAndConquer_soln model *)

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
    compose (solve_def (decomposeL d)) (solve_def (decomposeR d)).
intros.
apply smaller_decomposeR; assumption.
apply smaller_decomposeL; assumption.
apply smaller_wf.
Defined.

Theorem solve_correct : (forall d, IO d (solve_def d)).
intros.
functional induction (solve_def d).
apply direct_solve_correct; assumption.
apply decompose_compose_correct; assumption.
Qed.

End Solver.


(***
 *** Interpretation from problem spec to solution spec
 ***)

Spec Interpretation DnC_interp : DivideAndConquer_problem -> DivideAndConquer_soln :=
  { solve +-> solve_def }.
Next Obligation.
constructor.
apply solve_correct.
Defined.
