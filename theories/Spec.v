
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

(* Build the ops for a spec from an op for the head and ops for the tail *)
Definition ops_cons {f T} {constraint:T -> Prop} {rest}
           (t:T) (pf:constraint t) (ops_rest:spec_ops (rest t pf)) :
  spec_ops (Spec_ConsOp f T constraint rest) :=
  existT _ t (existT _ pf ops_rest).

(* Project the first op of a spec *)
Definition ops_head {f T constraint rest}
           (ops: spec_ops (Spec_ConsOp f T constraint rest)) : T :=
  projT1 ops.

(* Project the proof that the first op of a spec meets its constraint *)
Definition ops_proof {f T constraint rest}
           (ops: spec_ops (Spec_ConsOp f T constraint rest)) :
  constraint (ops_head ops) :=
  projT1 (projT2 ops).

(* Project the tail of the ops of a spec *)
Definition ops_rest {f T constraint rest}
           (ops: spec_ops (Spec_ConsOp f T constraint rest)) :
  spec_ops (rest (ops_head ops) (ops_proof ops)) :=
  projT2 (projT2 ops).


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

(* An interpretation from spec1 into spec2 is a pair of functions that map the
ops and the models, respectively, of spec2 to those of spec1 *)
Definition Interpretation spec1 spec2 :=
  { ops_f: spec_ops spec2 -> spec_ops spec1 |
    forall ops, spec_model spec2 ops -> spec_model spec1 (ops_f ops) }.

(* Helper to build an interpretation from spec1 to spec2 *)
Definition mkInterp {spec1 spec2} ops_f model_f : Interpretation spec1 spec2 :=
  exist _ ops_f model_f.

(* Apply the ops map of an interpretation *)
Definition map_ops {spec1 spec2} (i:Interpretation spec1 spec2) :
  spec_ops spec2 -> spec_ops spec1 :=
  match i with exist _ ops_f model_f => ops_f end.

(* Apply the model map of an interpretation *)
Definition map_model {spec1 spec2} (i:Interpretation spec1 spec2) :
  forall ops2, spec_model spec2 ops2 -> spec_model spec1 (map_ops i ops2) :=
  match i with exist _ ops_f model_f => model_f end.

(* The identity interpretation *)
Definition interp_id (spec:Spec) : Interpretation spec spec :=
  mkInterp id (fun _ model => model).

(* Composing interpretations *)
Definition interp_compose {s1 s2 s3}
           (i2: Interpretation s2 s3) (i1: Interpretation s1 s2) :
  Interpretation s1 s3 :=
  mkInterp (fun ops3 => map_ops i1 (map_ops i2 ops3))
           (fun ops3 model3 => map_model i1 _ (map_model i2 _ model3)).

(* Build an interpretation between the tails of two specs that have the same
head into an interpretation between the whole of the two specs *)
Definition interp_cons f T (constraint: T -> Prop)
           {spec1 spec2 : forall t, constraint t -> Spec}
           (i: forall t pfs, Interpretation (spec1 t pfs) (spec2 t pfs)) :
  Interpretation (Spec_ConsOp f T constraint spec1)
                 (Spec_ConsOp f T constraint spec2) :=
  mkInterp (fun ops2 =>
              ops_cons (ops_head ops2) (ops_proof ops2)
                       (map_ops (i _ _) (ops_rest ops2)))
           (fun ops2 model2 =>
              map_model (i _ _) _ model2).


(*** Sub-Specs and Spec Substitution ***)

(* This states that spec2 has all the ops of spec1 in the same order, with
possibly some extras in between. We put it in Type so we can recurse on it *)
Inductive SubSpec : Spec -> Spec -> Type :=
| SubSpec_base axioms spec2 :
    (forall ops, spec_model spec2 ops -> conjoin_axioms axioms) ->
    SubSpec (Spec_Axioms axioms) spec2
| SubSpec_eq f T (constraint: T -> Prop) rest1 rest2 :
    (forall t pf, SubSpec (rest1 t pf) (rest2 t pf)) ->
    SubSpec (Spec_ConsOp f T constraint rest1)
            (Spec_ConsOp f T constraint rest2)
| SubSpec_neq spec1 f2 T2 (constraint2: T2 -> Prop) rest2 :
    (forall t2 pf2, SubSpec spec1 (rest2 t2 pf2)) ->
    SubSpec spec1 (Spec_ConsOp f2 T2 constraint2 rest2)
.

Fixpoint spec_subtract spec1 spec2 (sub: SubSpec spec1 spec2) :
  spec_ops spec1 -> Spec :=
  match sub in SubSpec spec1 spec2 return spec_ops spec1 -> Spec with
    | SubSpec_base axioms spec2 axioms_pf => fun _ => spec2
    | SubSpec_eq f T constraint rest1 rest2 sub' =>
      fun ops1 =>
        spec_subtract _ _ (sub' (ops_head ops1) (ops_proof ops1)) (ops_rest ops1)
    | SubSpec_neq spec1 f2 T2 constraint2 rest2 sub' =>
      fun ops1 =>
        Spec_ConsOp f2 T2 constraint2
                    (fun t2 pf2 =>
                       spec_subtract spec1 (rest2 t2 pf2) (sub' t2 pf2) ops1)
  end
.

Lemma spec_subtract_interp spec1 spec2 sub :
  forall ops1, Interpretation spec2 (spec_subtract spec1 spec2 sub ops1).
  induction sub; intros.
  apply interp_id.
  destruct (X _ _ (ops_rest ops1)) as [ops_f model_f].
  exists (fun ops_sub => ops_cons (ops_head ops1) (ops_proof ops1) (ops_f ops_sub)).
  apply model_f.
  unfold spec_subtract; fold spec_subtract.
  apply interp_cons. intros; apply X.
Qed.

Fixpoint spec_append_axioms spec axioms2 : Spec :=
  match spec with
    | Spec_Axioms axioms1 => Spec_Axioms (axioms1 ++ axioms2)
    | Spec_ConsOp f T constraint rest =>
      Spec_ConsOp f T constraint (fun t pf => spec_append_axioms (rest t pf) axioms2)
  end.

Fixpoint spec_append spec1 : (spec_ops spec1 -> Spec) -> Spec :=
  match spec1 return (spec_ops spec1 -> Spec) -> Spec with
    | Spec_Axioms axioms1 =>
      fun spec2 => spec_append_axioms (spec2 tt) axioms1
    | Spec_ConsOp f T constraint rest =>
      fun spec2 =>
        Spec_ConsOp f T constraint
                    (fun t pf =>
                       spec_append (rest t pf)
                                   (fun ops1 => spec2 (ops_cons t pf ops1)))
  end.
