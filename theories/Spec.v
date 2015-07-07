
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

(* A predicate on an op, where None represents the trivial True predicate *)
Definition OpPred T := option (T -> Prop).

(* Whether an op satisfies an OpPred *)
Definition sats_op_pred {T} (p: OpPred T) : T -> Prop :=
  match p with
    | Some pred => pred
    | None => fun _ => True
  end.

(* Allows writing "oppred t" instead of "sats_op_pred oppred t" *)
Coercion sats_op_pred : OpPred >-> Funclass.

(* The inductive representation of specs, indexed by the op fields *)
Inductive Spec : Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : Spec
(* The inductive case adds an op named f with zero or more definitions to the
rest of the spec, that can depend on any f equal to all the definitions *)
| Spec_ConsOp (f:Field) (T : Type) (oppred: OpPred T)
              (rest : forall t, oppred t -> Spec) : Spec
.

(* Make the field argument be parsed by Coq as a string *)
Arguments Spec_ConsOp f%string T oppred rest.


(*** Models ***)

(* Helper for conjoining all the axioms in an axiom list *)
Fixpoint conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_left (fun P1 f_P2 => and P1 (snd f_P2)) axioms True.

(* Build the type of the op of a spec *)
Fixpoint spec_ops spec : Type :=
  match spec with
    | Spec_Axioms axioms => unit
    | Spec_ConsOp f T oppred rest =>
      { t : T & {pf: oppred t & spec_ops (rest t pf)}}
  end.

(* Build the type of the models of spec as a nested dependent pair *)
Fixpoint spec_model spec : spec_ops spec -> Prop :=
  match spec return spec_ops spec -> Prop with
    | Spec_Axioms axioms =>
      fun _ => conjoin_axioms axioms
    | Spec_ConsOp f T oppred rest =>
      fun ops =>
        spec_model (rest (projT1 ops) (projT1 (projT2 ops)))
                   (projT2 (projT2 ops))
  end.

(* Build the ops for a spec from an op for the head and ops for the tail *)
Definition ops_cons {f T} {oppred: OpPred T} {rest}
           (t:T) (pf:oppred t) (ops_rest:spec_ops (rest t pf)) :
  spec_ops (Spec_ConsOp f T oppred rest) :=
  existT _ t (existT _ pf ops_rest).

(* Project the first op of a spec *)
Definition ops_head {f T oppred rest}
           (ops: spec_ops (Spec_ConsOp f T oppred rest)) : T :=
  projT1 ops.

(* Project the proof that the first op of a spec meets its oppred *)
Definition ops_proof {f T oppred rest}
           (ops: spec_ops (Spec_ConsOp f T oppred rest)) :
  oppred (ops_head ops) :=
  projT1 (projT2 ops).

(* Project the tail of the ops of a spec *)
Definition ops_rest {f T oppred rest}
           (ops: spec_ops (Spec_ConsOp f T oppred rest)) :
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
  Spec_ConsOp "n" nat None
              (fun n _ => Spec_Axioms [("gt1"%string, n > 1)]).

(* Example 2:  op n:nat := 2;  (no axioms) *)
Program Definition spec_repr_example_2 :=
  Spec_ConsOp "n" nat (Some (fun n => n = 2))
              (fun n _ => Spec_Axioms []).

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Program Definition spec_repr_example_3 :=
  Spec_ConsOp
    "T" Set (Some (fun T => T = nat))
    (fun T T__pf =>
       Spec_ConsOp "n" T None
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
Definition interp_cons f T (oppred: OpPred T)
           {spec1 spec2 : forall t, oppred t -> Spec}
           (i: forall t pfs, Interpretation (spec1 t pfs) (spec2 t pfs)) :
  Interpretation (Spec_ConsOp f T oppred spec1)
                 (Spec_ConsOp f T oppred spec2) :=
  mkInterp (fun ops2 =>
              ops_cons (ops_head ops2) (ops_proof ops2)
                       (map_ops (i _ _) (ops_rest ops2)))
           (fun ops2 model2 =>
              map_model (i _ _) _ model2).

(* Take an interpretation from spec1 to spec2 and cons an op onto spec2 *)
Definition interp_cons_r f T (oppred: OpPred T)
           {spec1} {spec2: forall t, oppred t -> Spec}
           (i: forall t pfs, Interpretation spec1 (spec2 t pfs)) :
  Interpretation spec1 (Spec_ConsOp f T oppred spec2) :=
  mkInterp (fun ops2 => map_ops (i (ops_head ops2) (ops_proof ops2)) (ops_rest ops2))
           (fun ops2 model2 => map_model (i (ops_head ops2) (ops_proof ops2)) _ model2).


(*** Appending Specs ***)

(* Append axioms to the end of a spec *)
Fixpoint spec_append_axioms spec axioms2 : Spec :=
  match spec with
    | Spec_Axioms axioms1 => Spec_Axioms (axioms1 ++ axioms2)
    | Spec_ConsOp f T oppred rest =>
      Spec_ConsOp f T oppred (fun t pf => spec_append_axioms (rest t pf) axioms2)
  end.

(* FIXME: get rid of the admit! *)
Lemma conjoin_axioms_append1 axioms1 axioms2 :
  conjoin_axioms (axioms1 ++ axioms2) -> conjoin_axioms axioms1.
  induction axioms1; intros.
  constructor.
  admit.
Qed.

(* FIXME: get rid of the admit! *)
Lemma conjoin_axioms_append2 axioms1 axioms2 :
  conjoin_axioms (axioms1 ++ axioms2) -> conjoin_axioms axioms2.
  induction axioms1; intros.
  assumption.
  admit.
Qed.

(* The interpretation from any spec to the result of appending axioms to it *)
Fixpoint append_axioms_interp1 spec axioms2 :
  Interpretation spec (spec_append_axioms spec axioms2) :=
  match spec return Interpretation spec (spec_append_axioms spec axioms2) with
    | Spec_Axioms axioms1 =>
      mkInterp 
        (spec1:=Spec_Axioms axioms1) (spec2:=Spec_Axioms (axioms1++axioms2))
        id (fun _ model => conjoin_axioms_append1 axioms1 axioms2 model)
    | Spec_ConsOp f T oppred rest =>
      interp_cons f T oppred (fun t pf => append_axioms_interp1 (rest t pf) axioms2)
  end.

(* The interpretation from axioms to the result of appending them to a spec *)
Fixpoint append_axioms_interp2 spec axioms2 :
  Interpretation (Spec_Axioms axioms2) (spec_append_axioms spec axioms2) :=
  match spec return Interpretation (Spec_Axioms axioms2) (spec_append_axioms spec axioms2) with
    | Spec_Axioms axioms1 =>
      mkInterp
        (spec1:=Spec_Axioms axioms2) (spec2:=Spec_Axioms (axioms1++axioms2))
        (fun _ => tt)
        (fun _ model => conjoin_axioms_append2 axioms1 axioms2 model)
    | Spec_ConsOp f T oppred rest =>
      interp_cons_r f T oppred
                    (fun t pf => append_axioms_interp2 (rest t pf) axioms2)
  end.

(* Append one spec after another, where the spec being appended can depend on
the ops of the spec it is coming after *)
Fixpoint spec_append spec1 : (spec_ops spec1 -> Spec) -> Spec :=
  match spec1 return (spec_ops spec1 -> Spec) -> Spec with
    | Spec_Axioms axioms1 =>
      fun spec2 => spec_append_axioms (spec2 tt) axioms1
    | Spec_ConsOp f T oppred rest =>
      fun spec2 =>
        Spec_ConsOp f T oppred
                    (fun t pf =>
                       spec_append (rest t pf)
                                   (fun ops1 => spec2 (ops_cons t pf ops1)))
  end.

(* The interpretation from a spec to the result of appending another spec to it *)
Fixpoint interp_append1 spec1 :
  forall spec2, Interpretation spec1 (spec_append spec1 spec2) :=
  match spec1 return
        forall spec2, Interpretation spec1 (spec_append spec1 spec2) with
    | Spec_Axioms axioms1 =>
      fun spec2 => append_axioms_interp2 (spec2 tt) axioms1
    | Spec_ConsOp f T oppred rest =>
      fun spec2 =>
        interp_cons f T oppred
                    (fun t pf =>
                       interp_append1 (rest t pf)
                                      (fun ops1 => spec2 (ops_cons t pf ops1)))
  end.

(* The interpretation from a spec to the result of appending another spec to it *)
Definition interp_prepend_r spec spec1 :
  forall spec2, (forall ops1, Interpretation spec (spec2 ops1)) ->
                Interpretation spec (spec_append spec1 spec2).
  induction spec1; intros.
  apply (interp_compose (s2:=spec2 tt)).
  apply append_axioms_interp1.
  apply X.
  apply interp_cons_r; intros; fold spec_append. apply X. intros. apply X0.
Defined.


(*** Sub-Specs and Spec Substitution ***)

(* This states that spec2 has all the ops of spec1 in the same order, with
possibly some extras in between. We put it in Type so we can recurse on it *)
Inductive SubSpec : Spec -> Spec -> Type :=
| SubSpec_base axioms spec2 :
    (forall ops, spec_model spec2 ops -> conjoin_axioms axioms) ->
    SubSpec (Spec_Axioms axioms) spec2
| SubSpec_eq f T (oppred: OpPred T) rest1 rest2 :
    (forall t pf, SubSpec (rest1 t pf) (rest2 t pf)) ->
    SubSpec (Spec_ConsOp f T oppred rest1)
            (Spec_ConsOp f T oppred rest2)
| SubSpec_neq spec1 f2 T2 (oppred2: OpPred T2) rest2 :
    (forall t2 pf2, SubSpec spec1 (rest2 t2 pf2)) ->
    SubSpec spec1 (Spec_ConsOp f2 T2 oppred2 rest2)
.

(* Subtract sub-spec spec1 from super-spec spec2, given ops for spec1 *)
Fixpoint spec_subtract spec1 spec2 (sub: SubSpec spec1 spec2) :
  spec_ops spec1 -> Spec :=
  match sub in SubSpec spec1 spec2 return spec_ops spec1 -> Spec with
    | SubSpec_base axioms spec2 axioms_pf => fun _ => spec2
    | SubSpec_eq f T oppred rest1 rest2 sub' =>
      fun ops1 =>
        spec_subtract _ _ (sub' (ops_head ops1) (ops_proof ops1)) (ops_rest ops1)
    | SubSpec_neq spec1 f2 T2 oppred2 rest2 sub' =>
      fun ops1 =>
        Spec_ConsOp f2 T2 oppred2
                    (fun t2 pf2 =>
                       spec_subtract spec1 (rest2 t2 pf2) (sub' t2 pf2) ops1)
  end
.

(* There is an interpretation from spec2 to spec2 minus spec1 *)
Fixpoint spec_subtract_interp spec1 spec2 sub :
  forall ops1, Interpretation spec2 (spec_subtract spec1 spec2 sub ops1) :=
  match sub in SubSpec spec1 spec2
        return forall ops1,
                 Interpretation spec2 (spec_subtract spec1 spec2 sub ops1) with
    | SubSpec_base _ _ _ => fun _ => interp_id _
    | SubSpec_eq f T oppred rest1 rest2 sub' =>
      fun ops1 =>
        mkInterp (fun ops_sub =>
                    ops_cons (ops_head ops1) (ops_proof ops1)
                             (map_ops (spec_subtract_interp
                                         _ _ (sub' _ _) (ops_rest ops1))
                                      ops_sub))
                 (map_model (spec_subtract_interp _ _ _ (ops_rest ops1)))
    | SubSpec_neq spec1 f2 T2 oppred2 rest2 sub' =>
      fun ops1 =>
        interp_cons f2 T2 oppred2
                    (fun t2 pf2 =>
                       spec_subtract_interp _ _ (sub' t2 pf2) ops1)
  end.

(* Tactics-based proof of the above *)
(*
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
*)

(* Build a spec using spec substitution *)
Definition spec_subst {spec1sub spec1 spec2}
           (sub: SubSpec spec1sub spec1) (i: Interpretation spec1sub spec2) : Spec :=
  spec_append spec2
              (fun ops2 =>
                 spec_subtract spec1sub spec1 sub (map_ops i ops2)).

(* Build the interpretation from spec1 to the result of applying spec
substitution to spec1 *)
Definition spec_subst_interp1 {spec1sub spec1 spec2} sub i :
  Interpretation spec1 (@spec_subst spec1sub spec1 spec2 sub i).
  unfold spec_subst.
  apply interp_prepend_r; intros.
  apply spec_subtract_interp.
Defined.

(* Build the interpretation from spec2 to the result of applying any spec
substitution using an interpretation into spec2 *)
Definition spec_subst_interp2 {spec1sub spec1 spec2} sub i :
  Interpretation spec2 (@spec_subst spec1sub spec1 spec2 sub i) :=
  interp_append1 _ _.


(*** Types / Typeclasses Represented by Specs ***)

(* The type of Curried functions on the ops of spec *)
Fixpoint ForallOps spec : (spec_ops spec -> Type) -> Type :=
  match spec with
    | Spec_Axioms _ => fun body => body tt
    | Spec_ConsOp f T oppred rest =>
      fun body =>
        (match oppred return (forall t, sats_op_pred oppred t -> Type) -> Type with
           | None => fun F => forall t, F t I
           | Some pred => fun F => forall t pf, F t pf
         end)
        (fun t pf => ForallOps (rest t pf) (fun ops => body (ops_cons t pf ops)))
  end.

(* The type of Curried predicates on the ops of spec *)
Definition OpsPred spec : Type := ForallOps spec (fun _ => Prop).

(* Helper: all proofs of True are equal *)
Definition True_eq (pf1: True) : forall pf2, pf1 = pf2 :=
  match pf1 return forall pf2, pf1 = pf2 with
    | I => fun pf2 => match pf2 return I = pf2 with I => eq_refl end end.

(* Helper: all elements of type unit are equal *)
Definition tt_eq (u1: unit) : forall u2, u1 = u2 :=
  match u1 return forall u2, u1 = u2 with
    | tt => fun u2 => match u2 return tt = u2 with tt => eq_refl end end.

(* Apply a Curried predicate to some candidate ops for spec *)
Fixpoint apply_to_ops spec : forall ops body, ForallOps spec body -> body ops :=
  match spec return forall ops body, ForallOps spec body -> body ops with
    | Spec_Axioms _ => fun ops body F => rew [body] (tt_eq _ _) in F
    | Spec_ConsOp f T oppred rest =>
      fun ops =>
        match ops return forall body, ForallOps (Spec_ConsOp f T oppred rest) body -> body ops with
          | existT _ t (existT _ pf orest) =>
            fun body F =>
              apply_to_ops
                (rest t pf) orest
                _
                ((match oppred
                        return forall t pf rest' body',
                                 ForallOps (Spec_ConsOp f T oppred rest') body' ->
                                 ForallOps (rest' t pf)
                                           (fun ops => body' (ops_cons t pf ops)) with
                    | None => fun t pf rest' body' F => rew (True_eq _ _) in (F t)
                    | Some pred => fun t pf rest' body' F => F t pf
                  end) t pf rest
                       body F)
        end
  end.

(* Whether P is isomorphic to spec *)
Class IsoToSpec {spec} (P: OpsPred spec) : Prop :=
  spec_iso: forall ops, apply_to_ops spec ops _ P <-> spec_model spec ops.


(*** Refinement ***)

Record RefinementOf spec : Type :=
  {ref_spec: Spec;
   ref_interp: Interpretation spec ref_spec;
   ref_others: list {spec' : Spec & Interpretation spec' ref_spec &
                                  {P:OpsPred spec' | @IsoToSpec spec' P }}}.
