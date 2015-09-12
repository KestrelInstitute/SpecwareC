
Add LoadPath "../theories" as Specware.
Require Import Specware.SpecwareC.


(* Base spec contains two natural numbers, n and m *)
Definition base : Spec :=
  Spec_Cons
    "n" nat Pred_Trivial
    (fun n n__proof =>
       Spec_Cons
         "m" nat Pred_Trivial
         (fun m m__proof => Spec_Axioms nil)).

(* spec1 contains just the natural nmber n *)
Definition spec1 : Spec :=
  Spec_Cons "n" nat Pred_Trivial (fun n n__proof => Spec_Axioms nil).

(* Interpretation that sets m to be 2 *)
Definition interp1 : Interpretation base spec1 :=
  fun model =>
    match model with
      | opCons n n__proof I =>
        opCons n n__proof (opCons (oppred:=Pred_Trivial) 2 I I)
    end.

(* spec2 contains just the natural nmber m *)
Definition spec2 : Spec :=
  Spec_Cons "m" nat Pred_Trivial (fun m m__proof => Spec_Axioms nil).

(* Interpretation that sets n to be 1 *)
Definition interp2 : Interpretation base spec2 :=
  fun model =>
    match model with
      | opCons m m__proof I =>
        opCons (oppred:=Pred_Trivial) 1 I (opCons m m__proof I)
    end.

(* Now: find a pushout of interp1 and interp2 *)
Definition pushout12 : Pushout interp1 interp2.
  pushout_tactic 0.
