
(*** Tactics for Refinement ***)

Add LoadPath "." as Specware.
Require Import Util.
Require Export Base.


(*** a Refinement of a spec is another spec and a morphism to it ***)
Definition Refinement {flds} (spec : Spec (flds:=flds)) :=
  { flds' : _ & { spec' : Spec (flds:=flds') & Morphism spec spec' }}.



(***  ***)
