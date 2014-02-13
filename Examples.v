
(**
 ** Some simple examples of specs and morphisms
 **)

Add LoadPath "." as Specware.
Require Import Refinement.


(* Our base spec: groups *)
Definition GroupSpec :=
  {#
    "G" ::: Set ; G =>
    "zero" ::: G ; _ =>
    "plus" ::: G -> G -> G ; _ =>
    end-spec
  #}.

(* The null refinement of GroupSpec *)
Definition GroupSpec' : Refinement GroupSpec.
  end_refine.
Defined.

Eval compute in (refinementSpec GroupSpec').

