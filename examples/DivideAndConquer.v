
Add LoadPath "../theories" as Specware.
Require Export Specware.SpecwareC.

(* Required for the "Function" mechanism used below *)
Require Import Recdef.
Require Import Coq.Program.Wf.


(***
 *** Binary Divide-and-Conquer Algorithms
 ***)

(* The base spec, containing all the helper ops *)
Spec DivideAndConquer_base.

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

Spec End DivideAndConquer_base.


(* The "specification" spec, with the solve variable and its specification *)
Spec DivideAndConquer_spec.

Spec Import DivideAndConquer_base.

 (* The solver *)
Spec Variable solve : (D -> R).
Spec Axiom solve_correct : (forall d, IO d (solve d)).

Spec End DivideAndConquer_spec.


(* The implementation spec, that defines the solver *)
Spec DivideAndConquer_impl.

Spec Import DivideAndConquer_base.

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

Spec Definition solve : (D -> R) := solve_def.


Spec Theorem solve_correct : (forall d, IO d (solve d)).
unfold solve; unfold def; intros.
functional induction (solve_def d).
apply direct_solve_correct; assumption.
apply solve_soundness.
rewrite e0; apply IHr.
rewrite e0; apply IHr0.
Qed.

Spec End DivideAndConquer_impl.

(* FIXME: this does not work when Load-ing this file...? *)
(*
Spec Interpretation dc_impl : DivideAndConquer_spec -> DivideAndConquer_impl.
prove_simple_interp {{ }}.
intros.
apply (DivideAndConquer_impl.solve_correct
         (solve__param:=t7) (solve__proof__param:=pf7) (solve_soundness__param:=axiom0) (direct_solve_correct__param:=axiom)).
Defined.
*)
