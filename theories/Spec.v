
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

(* Unfold a definition *)
Definition unfold_def {T x} (t:T) (t__pf: t = x) : T := x.


(*** Models ***)

(* Helper for conjoining all the axioms in an axiom list *)
Definition conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_right (fun f_P1 P2 => and (snd f_P1) P2) True axioms.

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
Program Definition spec_example_1 :=
  Spec_ConsOp "n" nat None
              (fun n _ => Spec_Axioms [("gt1"%string, n > 1)]).

(* Example 2:  op n:nat := 2;  (no axioms) *)
Program Definition spec_example_2 :=
  Spec_ConsOp "n" nat (Some (fun n => n = 2))
              (fun n _ => Spec_Axioms []).

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Program Definition spec_example_3 :=
  Spec_ConsOp
    "T" Set (Some (fun T => T = nat))
    (fun T T__pf =>
       Spec_ConsOp "n" (unfold_def T T__pf) None
                   (fun n _ => Spec_Axioms [("gt1"%string, n > 1)])).


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


(*** Example Interpretations ***)

(* Interpret T as nat and n as n for spec_example_3 into spec_example_2 *)
Program Definition interp_example_3_2 : Interpretation spec_example_3 spec_example_2 :=
  fun ops2 =>
    (ops_cons (oppred:= Some (fun T => T = nat)) nat eq_refl
              (ops_cons (oppred:=None) (ops_head ops2) I (tt : spec_ops (Spec_Axioms _)))) : spec_ops spec_example_3.
Print interp_example_3_2.
Check interp_example_3_2_obligation_1.


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
  destruct H; split.
  assumption.
  apply IHaxioms1. assumption.
Qed.

(* FIXME: get rid of the admit! *)
Lemma conjoin_axioms_append2 axioms1 axioms2 :
  conjoin_axioms (axioms1 ++ axioms2) -> conjoin_axioms axioms2.
  induction axioms1; intros.
  assumption.
  apply IHaxioms1. destruct H. assumption.
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

Definition ForallOp_indep T (oppred: OpPred T) (A:Type) : Type :=
  match oppred with
    | None => forall (t:T), A
    | Some pred => forall (t:T) (pf:oppred t), A
  end.

Definition LambdaOp_indep T oppred A :
  (forall t, sats_op_pred oppred t -> A) -> ForallOp_indep T oppred A :=
  match oppred return (forall t, sats_op_pred oppred t -> A) ->
                      ForallOp_indep T oppred A with
    | None => fun body t => body t I
    | Some pred => fun body t pf => body t pf
  end.

Definition ApplyOp_indep T (oppred: OpPred T) A : (forall t, oppred t -> A) ->
                                                  forall t, oppred t -> A :=
  match oppred return (forall t, sats_op_pred oppred t -> A) ->
                      forall t, sats_op_pred oppred t -> A with
    | None => fun F t pf => F t I
    | Some pred => fun F t pf => F t pf
  end.

Definition ForallOp T (oppred: OpPred T) : (forall t, oppred t -> Type) -> Type :=
  match oppred return (forall t, sats_op_pred oppred t -> Type) -> Type with
    | None => fun A => forall t, A t I 
    | Some pred => fun A => forall t pf, A t pf
  end.

Definition LambdaOp T oppred : forall body_tp, (forall t pf, body_tp t pf) ->
                                               ForallOp T oppred body_tp :=
  match oppred return forall body_tp, (forall t pf, body_tp t pf) ->
                                      ForallOp T oppred body_tp with
    | None => fun body_tp body => fun t => body t I
    | Some pred => fun body_tp body => fun t pf => body t pf
  end.

Definition ApplyOp_type T (oppred: OpPred T) : (forall t, oppred t -> Type) ->
                                               forall t, oppred t -> Type :=
  match oppred return (forall t, sats_op_pred oppred t -> Type) ->
                      forall t, sats_op_pred oppred t -> Type with
    | None => fun body_tp t pf => body_tp t I
    | Some pred => fun body_tp t pf => body_tp t pf
  end.

Definition ApplyOp T (oppred: OpPred T) :
  forall body_tp, (forall t pf, body_tp t pf) ->
                  forall t pf,
                    ApplyOp_type T oppred body_tp t pf :=
  match oppred return forall body_tp, (forall t pf, body_tp t pf) ->
                                      forall t pf,
                                        ApplyOp_type T oppred body_tp t pf with
    | None => fun body_tp body t pf => body t I
    | Some pred => fun body_tp body t pf => body t pf
  end.

(* The type of Curried functions on the ops of spec *)
Fixpoint ForallOps spec : (spec_ops spec -> Type) -> Type :=
  match spec with
    | Spec_Axioms _ => fun body_tp => body_tp tt
    | Spec_ConsOp f T oppred rest =>
      fun body_tp =>
        ForallOp T oppred
                 (fun t pf => ForallOps (rest t pf)
                                        (fun ops => body_tp (ops_cons t pf ops)))
  end.

(* The type of Curried predicates on the ops of spec *)
Definition OpsPred spec : Type := ForallOps spec (fun _ => Prop).

(* Build a ForallOps function *)
Fixpoint LambdaOps spec : forall body_tp, (forall ops, body_tp ops) ->
                                          ForallOps spec body_tp :=
  match spec return forall body_tp, (forall ops, body_tp ops) ->
                                    ForallOps spec body_tp with
    | Spec_Axioms _ =>
      fun body_tp body => body tt
    | Spec_ConsOp f T oppred rest =>
      fun body_tp body =>
        LambdaOp T oppred _
                 (fun t pf =>
                    LambdaOps (rest t pf) _ (fun ops => body (ops_cons t pf ops)))
  end.

(* Apply a Curried predicate to some candidate ops for spec *)
Fixpoint ApplyOps_indep spec A : (ForallOps spec (fun _ => A)) -> spec_ops spec -> A :=
  match spec return (ForallOps spec (fun _ => A)) -> spec_ops spec -> A with
    | Spec_Axioms _ => fun body ops => body
    | Spec_ConsOp f T oppred rest =>
      fun body ops =>
        FIXME HERE

        ApplyOps_indep
          (rest (ops_head ops) (ops_proof ops)) A
          ((match oppred return ForallOp T oppred (fun _ _ => A) -> A with
              | None => fun F => F (ops_head ops)
              | Some pred => fun F => F (ops_head ops) (ops_proof ops)
            end))

        ApplyOp_indep T oppred _
                     (fun t pf => ApplyOps_indep (rest t pf) A
                                                 (fun ops => body (ops_cons t pf ops))
                                                 (ops_rest ops))
  end.

(* Helper: all proofs of True are equal *)
Definition True_eq (pf1: True) : forall pf2, pf1 = pf2 :=
  match pf1 return forall pf2, pf1 = pf2 with
    | I => fun pf2 => match pf2 return I = pf2 with I => eq_refl end end.

(* Helper: all elements of type unit are equal *)
Definition tt_eq (u1: unit) : forall u2, u1 = u2 :=
  match u1 return forall u2, u1 = u2 with
    | tt => fun u2 => match u2 return tt = u2 with tt => eq_refl end end.

(* Apply a Curried predicate to some candidate ops for spec *)
Fixpoint apply_to_ops spec : forall body_tp, ForallOps spec body_tp ->
                                             forall ops, body_tp ops :=
  match spec return forall body_tp, ForallOps spec body_tp ->
                                    forall ops, body_tp ops with
    | Spec_Axioms _ =>
      fun body_tp F ops => rew [body_tp] (tt_eq _ _) in F
    | Spec_ConsOp f T oppred rest =>
      fun body_tp F ops =>
        apply_to_ops
          (rest (ops_head ops) (ops_proof ops))
          _
          ((match oppred return forall rest' body_tp',
                                  ForallOps (Spec_ConsOp f T oppred rest') body_tp' ->
                                  (forall t (pf:sats_op_pred oppred t),
                                     ForallOps (rest' t pf)
                                               (fun ops => body_tp' (ops_cons t pf ops)))
            with
              | None => fun rest' body_tp' body' => fun t pf => body' t
              | Some pred => fun rest' body_tp' body' => fun t pf => body' t pf
            end) rest body_tp F (ops_head ops) (ops_proof ops))
          (ops_rest ops)
  end.

(* Whether P is isomorphic to spec *)
Class IsoToSpec {spec} (P: OpsPred spec) : Prop :=
  spec_iso: forall ops, apply_to_ops spec ops _ P <-> spec_model spec ops.

(* Turn an interpretation from spec1 to spec2 into a function from a predicate
isomorphic to spec2 to a predicate ismorphic to spec1 *)
Definition mkIsoInterp {spec1 P1} {iso1: @IsoToSpec spec1 P1}
           {spec2 P2} {iso2: @IsoToSpec spec2 P2}
           (i: Interpretation spec1 spec2) :
  ForallOps spec2 (fun ops2 => spec_model spec2 ops2 ->
                               spec_model spec1 (map_ops i ops2)) :=
  LambdaOps spec2 _ (fun ops2 model2 => map_model i ops2 model2).


(*** Examples of Isomorphic Interpretations ***)

(* Example 1:  op n:nat;  axiom gt1: n > 1 *)
Class spec_example_1_class (n:nat) : Prop :=
  { example_1__gt1 : n > 1 }.

Instance iso_example_1 : @IsoToSpec spec_example_1 spec_example_1_class.
  intro ops; destruct ops as [n ops]; destruct ops as [pf_n ops]; destruct ops.
  destruct pf_n.
  compute.
  split.
  intro H; split; [ apply H | constructor ].
  intro H; destruct H. constructor. apply H.
Qed.

(* Example 2:  op n:nat := 2;  (no axioms) *)
Class spec_example_2_class (n:nat) (n__pf: n = 2) : Prop := { }.

Instance iso_example_2 : @IsoToSpec spec_example_2 spec_example_2_class.
  intro ops; destruct ops as [n ops]; destruct ops as [n__pf ops]; destruct ops.
  compute. split.
  intro; constructor.
  intro; constructor.
Qed.

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Class spec_example_3_class (T:Set) (T__pf: T = nat) (n: unfold_def T T__pf) : Prop :=
  { example_3__gt1 : n > 1 }.

Instance iso_example_3 : @IsoToSpec spec_example_3 spec_example_3_class.
  intro ops; destruct ops as [T ops]; destruct ops as [T__pf ops];
  destruct ops as [n ops]; destruct ops as [n__pf ops]; destruct ops.
  destruct n__pf.
  compute. split.
  intro H; split; [ destruct H; assumption | constructor ].
  intro H; destruct H; constructor; assumption.
Qed.


FIXME HERE: this needs work!

Instance iso_interp_example_3_2 : forall `{spec_example_2_class}, spec_example_3_class _ _ _ :=
  mkIsoInterp (interp_example_3_2).


(*** Refinement ***)

Record RefinementOf spec : Type :=
  {ref_spec: Spec;
   ref_interp: Interpretation spec ref_spec;
   ref_others: list {spec' : Spec & Interpretation spec' ref_spec &
                                  {P:OpsPred spec' | @IsoToSpec spec' P }}}.
