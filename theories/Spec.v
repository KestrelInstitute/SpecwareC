
(*** Modeling specs and interpretations as Coq terms ***)

Require Import List.
Import ListNotations.
Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Import EqNotations.


(*** Fields ***)

(* We define the type of fields in one place, so we can change it later *)
Definition Field : Set := string.
Definition Field_dec : forall (f1 f2 : Field), {f1=f2} + {f1<>f2} := string_dec.

Lemma Field_dec_eq f : { e : f = f | Field_dec f f = left e }.
  destruct (Field_dec f f).
  exists e; reflexivity.
  elimtype False; apply n; reflexivity.
Qed.

Lemma Field_dec_neq f f' : f <> f' -> { neq : f <> f' | Field_dec f f' = right neq }.
  destruct (Field_dec f f'); intros.
  elimtype False; apply (H e).
  exists n; reflexivity.
Qed.


(*** Specs ***)

(* The inductive representation of specs, indexed by the op fields *)
Inductive Spec : Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : Spec
(* The inductive case adds an op named f with zero or more definitions to the
rest of the spec, that can depend on any f equal to all the definitions *)
| Spec_ConsOp (f:Field) (T : Type) (constraint: T -> Prop)
              (rest : forall t, constraint t -> Spec) : Spec
.

(* Make the field argument be parsed by Coq as a string *)
Arguments Spec_ConsOp f%string T constraint rest.


(*** Models ***)

(* Helper for conjoining all the axioms in an axiom list *)
Fixpoint conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_left (fun P1 f_P2 => and P1 (snd f_P2)) axioms True.

(* Build the type of the op of a spec *)
Fixpoint spec_ops spec : Type :=
  match spec with
    | Spec_Axioms axioms => unit
    | Spec_ConsOp f T constraint rest =>
      { t : T & {pf: constraint t & spec_ops (rest t pf)}}
  end.

(* Build the type of the models of spec as a nested dependent pair *)
Fixpoint spec_model spec : spec_ops spec -> Prop :=
  match spec return spec_ops spec -> Prop with
    | Spec_Axioms axioms =>
      fun _ => conjoin_axioms axioms
    | Spec_ConsOp f T constraint rest =>
      fun ops =>
        spec_model (rest (projT1 ops) (projT1 (projT2 ops)))
                   (projT2 (projT2 ops))
  end.


(*** Spec Examples ***)

(* Helper notation for building specs (FIXME) *)
(*
Notation "'DeclOp' f T rest" := (Spec_DeclOp f%string $(solve_not_in_list)$ T rest)
  (at level 0, f at level 0, T at level 0, rest at level 0).
Notation "'DefOp' f T t rest" := (Spec_DefOp f $(solve_not_in_list)$ T rest) (at level 0).
*)
(*
Notation "'Axioms f1 t1 ; .. ; fn tn'" :=
  (Spec_Axioms (cons (f1, t1) .. (cons (fn, tn) nil)))
  (at level 0).
*)

(* Example 1:  op n:nat;  axiom gt1: n > 1 *)
Program Definition spec_repr_example_1 :=
  Spec_ConsOp "n" nat (fun _ => True)
              (fun n _ => Spec_Axioms [("gt1"%string, n > 1)]).

(* Example 2:  op n:nat := 2;  (no axioms) *)
Program Definition spec_repr_example_2 :=
  Spec_ConsOp "n" nat (fun n => n = 2)
              (fun n _ => Spec_Axioms []).

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Program Definition spec_repr_example_3 :=
  Spec_ConsOp
    "T" Set (fun T => T = nat)
    (fun T T__pf =>
       Spec_ConsOp "n" T (fun _ => True)
                   (fun n _ => Spec_Axioms [("gt1"%string, (rew T__pf in n) > 1)])).
Next Obligation.
exact x.
Defined.
Print spec_repr_example_3.


(*** Interpretations ***)

Definition Interpretation spec1 spec2 :=
  { ops_f: spec_ops spec2 -> spec_ops spec1 |
    forall ops, spec_model spec2 ops -> spec_model spec1 (ops_f ops) }.

(* The identity interpretation *)
Definition interp_id (spec:Spec) : Interpretation spec spec :=
  exist (fun ops_f => forall ops, spec_model spec ops -> spec_model spec (ops_f ops)) (fun x => x) (fun _ model => model).

