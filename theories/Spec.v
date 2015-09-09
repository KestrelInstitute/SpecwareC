(* Copyright (c) 2015, Kestrel Institute
All rights reserved.

This program is free software; you can redistribute it and/or modify it under
the terms of the included LICENSE.txt file.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the LICENSE.txt for more details. *)


(*** Modeling specs and interpretations as Coq terms ***)

Require Import List.
Import ListNotations.
Require Export String.
Require Import Coq.Logic.Eqdep_dec.
Import EqNotations.
Require Import Coq.Arith.Lt.


(*** Misc Helper Functions ***)

(* The nth element of a list *without* a default *)
Fixpoint nth_nodef {A} n (l: list A) {struct l} : n < List.length l -> A :=
  match l return n < List.length l -> A with
    | nil => fun pf => match lt_n_0 _ pf with end
    | x::l' =>
      match n with
        | 0 => fun _ => x
        | S n' => fun pf => nth_nodef n' l' (lt_S_n _ _ pf)
      end
  end.


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

(* Subtype predicates on ops, which include:
   + The trivial True predicate;
   + An equality to an existing object; and
   + An arbitrary functional predicate
 *)
Inductive OpPred (T:Type) : Type :=
| Pred_Trivial
| Pred_Eq (t':T)
| Pred_Fun (P:T -> Prop)
.

Arguments Pred_Trivial {T}.
Arguments Pred_Eq {T} t'.
Arguments Pred_Fun {T} P.

(* Whether an op satisfies an OpPred *)
Definition sats_op_pred {T} (p: OpPred T) : T -> Prop :=
  match p with
    | Pred_Trivial => fun _ => True
    | Pred_Eq t' => fun t => t = t'
    | Pred_Fun P => P
  end.

(* Allows writing "oppred t" instead of "sats_op_pred oppred t" *)
Coercion sats_op_pred : OpPred >-> Funclass.

(* The type of the representation of an axiom in a spec *)
Inductive SpecAxiom : Type :=
| specAxiom (f:Field) (P:Prop)
.

Arguments specAxiom f%string P%type.

(* Projections of SpecAxiom *)
Definition axiom_name (ax:SpecAxiom) :=
  let (f,_) := ax in f.
Definition axiom_prop (ax:SpecAxiom) :=
  let (_,P) := ax in P.

(* The inductive representation of specs, indexed by the op fields *)
Inductive Spec : Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list SpecAxiom) : Spec
(* The inductive case adds an op named f with zero or more definitions to the
rest of the spec, that can depend on any f equal to all the definitions *)
| Spec_Cons (f:Field) (T : Type) (oppred: OpPred T)
              (rest : forall t, oppred t -> Spec) : Spec
.

(* Make the field argument be parsed by Coq as a string *)
Arguments Spec_Cons f%string T oppred rest.

(* Unfold a definition *)
Definition def {T x} (t:T) (t__pf: t = x) : T := x.


(*** Models ***)

(* Helper for conjoining all the axioms in an axiom list *)
Fixpoint conjoin_axioms (axioms : list SpecAxiom) : Prop :=
  match axioms with
    | [] => True
    | [specAxiom _ P] => P
    | (specAxiom _ P) :: axioms' => P /\ conjoin_axioms axioms'
  end.

(* Helper for proving conjoin_axioms applied to a cons *)
Lemma conjoin_axioms_cons f (P:Prop) axioms :
  P -> conjoin_axioms axioms -> conjoin_axioms (specAxiom f P :: axioms).
  intros; destruct axioms; try split; assumption.
Qed.

(* Helper for destructing conjoin_axioms applied to a cons *)
Lemma conjoin_axioms_destruct f (P:Prop) axioms :
  conjoin_axioms (specAxiom f P :: axioms) -> P /\ conjoin_axioms axioms.
  intro H; destruct axioms; try (destruct H); split; try assumption; try constructor.
Qed.

(* The type of an op of type T, a proof of its oppred, and some further type U
that depends on the op; this is essentially a doubly nested dependent pair. *)
Inductive OpCons (T:Type) (oppred:OpPred T)
          (U: forall t, oppred t -> Type) : Type :=
| opCons (t:T) (pf:oppred t) (model':U t pf)
.

Arguments opCons {T oppred U} t pf model'.

(* Build the type of the models of spec as a nested dependent pair *)
Fixpoint spec_model spec : Type :=
  match spec with
    | Spec_Axioms axioms => conjoin_axioms axioms
    | Spec_Cons f T oppred rest =>
      OpCons T oppred (fun t pf => spec_model (rest t pf))
  end.

(* Project the first op of a spec *)
Definition model_head {f T oppred rest}
           (model: spec_model (Spec_Cons f T oppred rest)) : T :=
  match model with
    | opCons t pf model' => t
  end.

(* Project the proof that the first op of a spec meets its oppred *)
Definition model_proof {f T oppred rest}
           (model: spec_model (Spec_Cons f T oppred rest)) :
  oppred (model_head model) :=
  match model with
    | opCons t pf model' => pf
  end.

(* Project the tail of the model of a spec *)
Definition model_rest {f T oppred rest}
           (model: spec_model (Spec_Cons f T oppred rest)) :
  spec_model (rest (model_head model) (model_proof model)) :=
  match model with
    | opCons t pf model' => model'
  end.

(* The type of just the ops of spec, with no axiom proofs *)
Fixpoint spec_ops spec : Type :=
  match spec with
    | Spec_Axioms axioms => unit
    | Spec_Cons f T oppred rest =>
      OpCons T oppred (fun t pf => spec_ops (rest t pf))
  end.

(* Extract just the ops from a model of a spec *)
Fixpoint extract_spec_ops {spec} : spec_model spec -> spec_ops spec :=
  match spec return spec_model spec -> spec_ops spec with
    | Spec_Axioms axioms => fun _ => tt
    | Spec_Cons f T oppred rest =>
      fun model =>
        let (t,pf,model') := model in
        opCons t pf (extract_spec_ops model')
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
Definition spec_example_1 :=
  Spec_Cons "n" nat Pred_Trivial
              (fun n _ => Spec_Axioms [specAxiom "gt1" (n > 1)]).

(* Example 2:  op n:nat := 2;  (no axioms) *)
Definition spec_example_2 :=
  Spec_Cons "n" nat (Pred_Eq 2)
              (fun n _ => Spec_Axioms []).

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Definition spec_example_3 :=
  Spec_Cons
    "T" Set (Pred_Eq nat)
    (fun T T__pf =>
       Spec_Cons "n" (def T T__pf) Pred_Trivial
                   (fun n _ => Spec_Axioms [specAxiom "gt1" (n > 1)])).

(* Example 4: Monoids *)
Definition spec_example_monoid :=
  Spec_Cons
    "T" Set Pred_Trivial
    (fun T _ =>
       Spec_Cons
         "m_zero" T Pred_Trivial
         (fun m_zero _ =>
            Spec_Cons
              "m_plus" (T -> T -> T) Pred_Trivial
              (fun m_plus _ =>
                 Spec_Axioms
                   [specAxiom "m_zero_left" (forall x, m_plus m_zero x = x);
                     specAxiom "m_zero_right" (forall x, m_plus x m_zero = x);
                     specAxiom "m_plus_assoc"
                             (forall x y z,
                                m_plus x (m_plus y z) = m_plus (m_plus x y) z)]))).

(* Example 5: Groups *)
Definition spec_example_group :=
  Spec_Cons
    "T" Set Pred_Trivial
    (fun T _ =>
       Spec_Cons
         "g_zero" T Pred_Trivial
         (fun g_zero _ =>
            Spec_Cons
              "g_plus" (T -> T -> T) Pred_Trivial
              (fun g_plus _ =>
                 Spec_Cons
                   "g_inv" (T -> T) Pred_Trivial
                   (fun g_inv _ =>
                        Spec_Axioms
                          [specAxiom "g_zero_left" (forall x, g_plus g_zero x = x);
                            specAxiom "g_zero_right" (forall x, g_plus x g_zero = x);
                            specAxiom "g_plus_assoc"
                                    (forall x y z,
                                       g_plus x (g_plus y z) = g_plus (g_plus x y) z);
                            specAxiom "g_inv_left"
                                    (forall (x:T), g_plus (g_inv x) x = g_zero);
                            specAxiom "g_inv_right"
                                    (forall (x:T), g_plus x (g_inv x) = g_zero)
    ])))).

(* Example 6: The Natural Numbers as a Monoid *)
Definition spec_example_natmonoid :=
Spec_Cons "T" Type (@Pred_Eq Type nat)
  (fun T__param T__proof =>
   Spec_Cons "m_zero" (def T__param T__proof) (Pred_Eq 0)
     (fun m_zero__param m_zero__proof =>
      Spec_Cons "m_plus"
        (def T__param T__proof ->
         def T__param T__proof -> def T__param T__proof) 
        (Pred_Eq Nat.add)
        (fun m_plus__param m_plus__proof
         =>
         Spec_Axioms
           (specAxiom "m_zero_left"
              (forall x : def T__param T__proof,
               def m_plus__param m_plus__proof
                 (def m_zero__param m_zero__proof) x = x)
            :: (specAxiom "m_zero_right"
                  (forall x : def T__param T__proof,
                   def m_plus__param m_plus__proof x
                     (def m_zero__param m_zero__proof) = x)
                :: specAxiom "m_plus_assoc"
                     (forall x y z : def T__param T__proof,
                      def m_plus__param m_plus__proof x
                        (def m_plus__param m_plus__proof y z) =
                      def m_plus__param m_plus__proof
                        (def m_plus__param m_plus__proof x y) z) :: nil)%list)))).

Definition spec_example_model_natmonoid
           T__param T__proof m_zero__param m_zero__proof m_plus__param m_plus__proof
           (m_zero_left__param :
              forall x : def T__param T__proof,
               def m_plus__param m_plus__proof
                 (def m_zero__param m_zero__proof) x = x)
           (m_zero_right__param :
              forall x : def T__param T__proof,
               def m_plus__param m_plus__proof
                 x (def m_zero__param m_zero__proof) = x)
           (m_plus_assoc__param :
              forall x y z : def T__param T__proof,
                def m_plus__param m_plus__proof x
                    (def m_plus__param m_plus__proof y z) =
                def m_plus__param m_plus__proof
                    (def m_plus__param m_plus__proof x y) z) :
  spec_model spec_example_natmonoid :=
  @opCons
    _ (Pred_Eq (nat:Type)) _ T__param T__proof
    (@opCons
       _ (Pred_Eq 0) _ m_zero__param m_zero__proof
       (@opCons
          _ (Pred_Eq plus) _ m_plus__param m_plus__proof
          (conj m_zero_left__param
                (conj m_zero_right__param m_plus_assoc__param)))).


(*** Interpretations ***)

(* An interpretation from spec1 into spec2 is a function from models of spec2 to
models of spec1 where the returned ops for spec2 do not depend on the proofs of
the axioms of spec1; this condition is formalized by saying that there is a
function from the ops of spec2 to those of spec1 that is related to the model
function by extract_spec_ops. *)
Inductive Interpretation spec1 spec2 :=
| mkInterp (model_f: spec_model spec2 -> spec_model spec1)
           (ops_f: spec_ops spec2 -> spec_ops spec1)
           (interp_pf: forall model2,
                         extract_spec_ops (model_f model2) =
                         ops_f (extract_spec_ops model2))
.

Arguments mkInterp {spec1 spec2} model_f ops_f interp_pf.

(* Apply the model function of an interpretation *)
Definition map_model {spec1 spec2} (i: Interpretation spec1 spec2) :
           spec_model spec2 -> spec_model spec1 :=
  let (model_f,_,_) := i in model_f.

(* Apply the ops function of an interpretation *)
Definition map_ops {spec1 spec2} (i: Interpretation spec1 spec2) :
           spec_ops spec2 -> spec_ops spec1 :=
  let (_,ops_f,_) := i in ops_f.

(* Extract the interp_pf from an interpretation *)
Definition get_interp_pf {spec1 spec2} (i: Interpretation spec1 spec2) :
  forall model2, extract_spec_ops (map_model i model2) =
                 map_ops i (extract_spec_ops model2) :=
  match i return forall model2, extract_spec_ops (map_model i model2) =
                                map_ops i (extract_spec_ops model2) with

    | mkInterp _ _ interp_pf => interp_pf
  end.

(* The identity interpretation *)
Program Definition interp_id (spec:Spec) : Interpretation spec spec :=
  mkInterp id _ _.

(* Composing interpretations *)
Program Definition interp_compose {s1 s2 s3}
           (i2: Interpretation s2 s3) (i1: Interpretation s1 s2) :
  Interpretation s1 s3 :=
  mkInterp (fun model3 => map_model i1 (map_model i2 model3))
           (fun ops3 => map_ops i1 (map_ops i2 ops3))
           _
.
Obligation 1.
destruct i1; destruct i2. unfold map_model, map_ops.
rewrite interp_pf. rewrite interp_pf0. reflexivity.
Qed.

(* Build an interpretation between the tails of two specs that have the same
head into an interpretation between the whole of the two specs *)
Program Definition interp_cons f T (oppred: OpPred T)
           {spec1 spec2 : forall t, oppred t -> Spec}
           (i: forall t pfs, Interpretation (spec1 t pfs) (spec2 t pfs)) :
  Interpretation (Spec_Cons f T oppred spec1)
                 (Spec_Cons f T oppred spec2) :=
  mkInterp (fun model2:spec_model (Spec_Cons f T oppred spec2) =>
              let (t,pf,rest) := model2 in
              opCons t pf (map_model (i _ _) rest))
           (fun ops2:spec_ops (Spec_Cons f T oppred spec2) =>
              let (t,pf,rest) := ops2 in
              opCons t pf (map_ops (i _ _) rest))
           _.
Obligation 1.
destruct model2. destruct (i t pf). unfold map_model, map_ops.
rewrite interp_pf. reflexivity.
Qed.

(* Take an interpretation from spec1 to spec2 and cons an op onto spec2 *)
Program Definition interp_cons_r f T (oppred: OpPred T)
           {spec1} {spec2: forall t, oppred t -> Spec}
           (i: forall t pfs, Interpretation spec1 (spec2 t pfs)) :
  Interpretation spec1 (Spec_Cons f T oppred spec2) :=
  mkInterp (fun model2:spec_model (Spec_Cons f T oppred spec2) =>
              let (t,pf,rest) := model2 in
              map_model (i t pf) rest)
           (fun ops2:spec_ops (Spec_Cons f T oppred spec2) =>
              let (t,pf,rest) := ops2 in
              map_ops (i t pf) rest)
           _.
Obligation 1.
destruct model2. destruct (i t pf). unfold map_model, map_ops.
rewrite interp_pf. reflexivity.
Qed.


(*** Example Interpretations ***)

(* Interpret T as nat and n as n for spec_example_3 into spec_example_2 *)
Program Definition interp_example_3_2__models :
  spec_model spec_example_2 -> spec_model spec_example_3 :=
  (fun (model2:spec_model spec_example_2) =>
     match model2 with
       | opCons n n__proof ax_proofs =>
         (opCons
            (oppred:=Pred_Eq nat) nat _
            (opCons (oppred:=Pred_Trivial) n _
                    _)) : spec_model spec_example_3
     end).

Program Definition interp_example_3_2 : Interpretation spec_example_3 spec_example_2 :=
  mkInterp
    interp_example_3_2__models
    (fun (ops2:spec_ops spec_example_2) =>
       match ops2 with
         | opCons n n__proof tt =>
           (opCons
              (oppred:=Pred_Eq nat) _ _
              (opCons (oppred:=Pred_Trivial) _ _ tt))
       end)
    (*
    (fun ops2 =>
       match ops2 with
         | opCons n n__proof ax_proofs =>
           (opCons
              (oppred:=Pred_Eq nat) nat eq_refl
              (opCons (oppred:=Pred_Trivial) n _
                      _))
       end)
     *)
    (fun (model:spec_model spec_example_2) =>
    $(repeat (let t := fresh t in
              let pf := fresh pf in
              destruct model as [t pf model]);
     reflexivity)$)
.


(*** Appending Specs ***)

(* Prepend axioms to the axioms already in a spec *)
Fixpoint spec_prepend_axioms axioms1 spec : Spec :=
  match spec with
    | Spec_Axioms axioms2 => Spec_Axioms (axioms1 ++ axioms2)
    | Spec_Cons f T oppred rest =>
      Spec_Cons f T oppred (fun t pf => spec_prepend_axioms axioms1 (rest t pf))
  end.

Lemma conjoin_axioms_prepend1 axioms1 axioms2 :
  conjoin_axioms (axioms1 ++ axioms2) -> conjoin_axioms axioms1.
  induction axioms1.
  intros; constructor.
  intros; destruct a; destruct (conjoin_axioms_destruct _ _ _ H).
  apply conjoin_axioms_cons; [ assumption | apply IHaxioms1; assumption ].
Qed.

Lemma conjoin_axioms_prepend2 axioms1 axioms2 :
  conjoin_axioms (axioms1 ++ axioms2) -> conjoin_axioms axioms2.
  induction axioms1; intros.
  assumption.
  apply IHaxioms1.
  destruct a; destruct (conjoin_axioms_destruct _ _ _ H); assumption.
Qed.

Lemma conjoin_axioms_prepend_inv axioms1 axioms2 :
  conjoin_axioms axioms1 -> conjoin_axioms axioms2 ->
  conjoin_axioms (axioms1 ++ axioms2).
  induction axioms1; intros.
  assumption.
  destruct a; destruct (conjoin_axioms_destruct _ _ _ H).
  apply conjoin_axioms_cons; [ | apply IHaxioms1 ]; assumption.
Qed.

(* The interpretation from axioms to the result of prepending them to a spec *)
Fixpoint prepend_axioms_interp1 axioms1 spec :
  Interpretation (Spec_Axioms axioms1) (spec_prepend_axioms axioms1 spec) :=
  match spec return Interpretation (Spec_Axioms axioms1) (spec_prepend_axioms axioms1 spec) with
    | Spec_Axioms axioms2 =>
      mkInterp
        (fun (model12 : spec_model (spec_prepend_axioms _ (Spec_Axioms _))) =>
           conjoin_axioms_prepend1 axioms1 axioms2 model12
           : spec_model (Spec_Axioms _))
        id (fun _ => eq_refl)
    | Spec_Cons f T oppred rest =>
      interp_cons_r f T oppred
                    (fun t pf => prepend_axioms_interp1 axioms1 (rest t pf))
  end.

(* The interpretation from any spec to the result of prepending axioms to it *)
Fixpoint prepend_axioms_interp2 axioms1 spec :
  Interpretation spec (spec_prepend_axioms axioms1 spec) :=
  match spec return Interpretation spec (spec_prepend_axioms axioms1 spec) with
    | Spec_Axioms axioms2 =>
      mkInterp (conjoin_axioms_prepend2 axioms1 axioms2
                : spec_model (Spec_Axioms _) -> spec_model (Spec_Axioms _))
               id (fun _ => eq_refl)
    | Spec_Cons f T oppred rest =>
      interp_cons f T oppred (fun t pf => prepend_axioms_interp2 axioms1 (rest t pf))
  end.

(* Append one spec after another, where the spec being appended can depend on
the ops of the spec it is coming after *)
Fixpoint spec_append spec1 : (spec_ops spec1 -> Spec) -> Spec :=
  match spec1 return (spec_ops spec1 -> Spec) -> Spec with
    | Spec_Axioms axioms1 =>
      fun spec2 => spec_prepend_axioms axioms1 (spec2 tt)
    | Spec_Cons f T oppred rest =>
      fun spec2 =>
        Spec_Cons f T oppred
                    (fun t pf =>
                       spec_append (rest t pf)
                                   (fun ops1 =>
                                      spec2 (opCons t pf ops1)))
  end.

(* The interpretation from a spec to the result of prepending another spec to it *)
Fixpoint interp_append1 spec1 :
  forall spec2, Interpretation spec1 (spec_append spec1 spec2) :=
  match spec1 return
        forall spec2, Interpretation spec1 (spec_append spec1 spec2) with
    | Spec_Axioms axioms1 =>
      fun spec2 => prepend_axioms_interp1 axioms1 (spec2 tt)
    | Spec_Cons f T oppred rest =>
      fun spec2 =>
        interp_cons f T oppred
                    (fun t pf =>
                       interp_append1 (rest t pf)
                                      (fun ops1 => spec2 (opCons t pf ops1)))
  end.

(* Extract a model for spec2 from a model for (spec_append spec1 spec2). This
function is essentially a dependent interpretation, i.e., an interpretation from
spec2 to (spec_append spec1 spec2) but where the contents of spec2 can depend on
the spec1 ops contained in the model for (spec_append spec1 spec2) that is
passed to the interpretation. *)
Fixpoint interp_append2_model spec1 :
  forall spec2 (model12: spec_model (spec_append spec1 spec2)),
    spec_model (spec2 (map_ops (interp_append1 spec1 spec2) (extract_spec_ops model12))) :=
  match spec1 with
    | Spec_Axioms axioms1 =>
      fun spec2 model12 =>
        match (map_ops (interp_append1 (Spec_Axioms _) spec2)
                       (extract_spec_ops model12)) as ops1
              return spec_model (spec2 ops1) with
          | tt => map_model (prepend_axioms_interp2 _ _) model12
        end
    | Spec_Cons f T oppred rest =>
      fun spec2 model12 =>
        match model12
              return spec_model
                       (spec2
                          (map_ops (interp_append1 _ spec2)
                                   (@extract_spec_ops
                                      (Spec_Cons f T oppred _)
                                      model12))) with
          | opCons t pf model12' =>
            interp_append2_model (rest t pf)
                                (fun ops1 => spec2 (opCons t pf ops1)) model12'
        end
  end.

(* The ops portion of interp_append2_model *)
Fixpoint interp_append2_ops spec1 :
  forall spec2 (ops12: spec_ops (spec_append spec1 spec2)),
    spec_ops (spec2 (map_ops (interp_append1 spec1 spec2) ops12)) :=
  match spec1 with
    | Spec_Axioms axioms1 =>
      fun spec2 ops12 =>
        match map_ops (interp_append1 (Spec_Axioms _) spec2) ops12 as ops1
              return spec_ops (spec2 ops1) with
          | tt => map_ops (prepend_axioms_interp2 _ _) ops12
        end
    | Spec_Cons f T oppred rest =>
      fun spec2 ops12 =>
        match ops12
              return spec_ops
                       (spec2 (map_ops (interp_append1 _ spec2) ops12)) with
          | opCons t pf ops12' =>
            interp_append2_ops (rest t pf)
                                (fun ops1 => spec2 (opCons t pf ops1)) ops12'
        end
  end.

(* The proof associated with interp_append2_model/ops *)
Lemma interp_append2_interp_pf spec1 spec2 model12 :
  extract_spec_ops (interp_append2_model spec1 spec2 model12) =
  interp_append2_ops spec1 spec2 (extract_spec_ops model12).
  revert spec2 model12; induction spec1; intros.
  unfold interp_append2_model, interp_append2_ops.
  destruct (map_ops (interp_append1 (Spec_Axioms axioms) spec2)
                    (extract_spec_ops model12)).
  apply (get_interp_pf _).
  admit. (* FIXME HERE NOW *)
Qed.


(*** Spec Overlap ***)

(* NotInSpec f spec is a proof that f is not used as an op name in spec *)
Inductive NotInSpec (f:Field) : Spec -> Prop :=
| NotInSpec_base axioms : NotInSpec f (Spec_Axioms axioms)
| NotInSpec_cons f' T oppred rest :
    f <> f' ->
    (forall t pf, NotInSpec f (rest t pf)) ->
    NotInSpec f (Spec_Cons f' T oppred rest)
.

(* Tactic to prove NotInSpec goals *)
Ltac prove_not_in_spec :=
  match goal with
    | |- NotInSpec ?f (Spec_Cons ?f' _ _ _) =>
      apply NotInSpec_cons; [ discriminate | intros; prove_not_in_spec ]
    | |- NotInSpec ?f (Spec_Axioms _) =>
      apply NotInSpec_base
  end.

(* Helper lemma to prove not in goals *)
Lemma not_in_cons {A} (x y:A) l :
  y <> x -> ~(In x l) -> ~(In x (y::l)).
  intros neq not_in in_xy.
  destruct in_xy; contradiction.
Qed.

(* Tactic to prove ~(In f l) goals *)
Ltac prove_not_in_list :=
  match goal with
    | |- ~(In ?f (cons ?f' ?l)) =>
      apply not_in_cons; [ discriminate | prove_not_in_list ]
    | |- ~(In ?f nil) =>
      apply in_nil
  end.

(* Helper type for SpecOverlap *)
Inductive AxiomOverlap : list SpecAxiom -> list SpecAxiom -> Type :=
| AxiomOverlap_base : AxiomOverlap [] []
| AxiomOverlap_eq ax_name ax_tp axioms1 axioms2 :
    AxiomOverlap axioms1 axioms2 ->
    AxiomOverlap (specAxiom ax_name ax_tp::axioms1)
                 (specAxiom ax_name ax_tp::axioms2)
| AxiomOverlap_neq1 ax_name ax_tp axioms1 axioms2 :
    ~(In ax_name (map axiom_name axioms2)) ->
    AxiomOverlap axioms1 axioms2 ->
    AxiomOverlap (specAxiom ax_name ax_tp::axioms1) axioms2
| AxiomOverlap_neq2 ax_name ax_tp axioms1 axioms2 :
    ~(In ax_name (map axiom_name axioms1)) ->
    AxiomOverlap axioms1 axioms2 ->
    AxiomOverlap axioms1 (specAxiom ax_name ax_tp::axioms2)
.

(* SpecOverlap spec1 spec2 is a correlation between spec1 and spec2 that
identifies some sequence of ops and axioms that occur in both spec1 and spec2 in
the same order and with the same types and subtype predictes. In fact, an
element of SpecOverlap spec1 spec2 is the maximal such sequence. *)
Inductive SpecOverlap : Spec -> Spec -> Type :=
| SpecOverlap_base axioms1 axioms2 :
    AxiomOverlap axioms1 axioms2 ->
    SpecOverlap (Spec_Axioms axioms1) (Spec_Axioms axioms2)
| SpecOverlap_eq f T oppred rest1 rest2 :
    (forall t pf, SpecOverlap (rest1 t pf) (rest2 t pf)) ->
    SpecOverlap (Spec_Cons f T oppred rest1) (Spec_Cons f T oppred rest2)
| SpecOverlap_neq1 f1 T1 oppred1 rest1 spec2 :
    NotInSpec f1 spec2 ->
    (forall t pf, SpecOverlap (rest1 t pf) spec2) ->
    SpecOverlap (Spec_Cons f1 T1 oppred1 rest1) spec2
| SpecOverlap_neq2 f2 T2 oppred2 rest2 spec1 :
    NotInSpec f2 spec1 ->
    (forall t pf, SpecOverlap spec1 (rest2 t pf)) ->
    SpecOverlap spec1 (Spec_Cons f2 T2 oppred2 rest2)
.

(* Tactic to prove AxiomOverlap *)
Ltac prove_axiom_overlap :=
  lazymatch goal with
    | |- AxiomOverlap (specAxiom ?ax_name1 ?ax_tp1 :: ?axioms1)
                      (specAxiom ?ax_name2 ?ax_tp2 :: ?axioms2) =>
      match eval hnf in (Field_dec ax_name1 ax_name2) with
        | left _ =>
          (apply AxiomOverlap_eq
                 || fail "Non-matching types at axiom" ax_name1);
          intros; prove_axiom_overlap
        | right ?neq =>
          ((apply AxiomOverlap_neq1; [ prove_not_in_list | ]) ||
           (apply AxiomOverlap_neq2; [ prove_not_in_list | ]) ||
           fail "The axioms " ax_name1 " and " ax_name2 " appear to be in a different order in the two axioms");
          prove_axiom_overlap
      end
    | |- AxiomOverlap (cons _ _) nil =>
      apply AxiomOverlap_neq1; [ apply in_nil | prove_axiom_overlap ]
    | |- AxiomOverlap nil (cons _ _) =>
      apply AxiomOverlap_neq2; [ apply in_nil | prove_axiom_overlap ]
    | |- AxiomOverlap nil nil =>
      apply AxiomOverlap_base
    | |- AxiomOverlap ?axioms1 ?axioms2 =>
      let axioms1_hnf := (eval hnf in axioms1) in
      let axioms2_hnf := (eval hnf in axioms2) in
      progress (change (AxiomOverlap axioms1_hnf axioms2_hnf)); prove_axiom_overlap
    | |- ?goal => fail "prove_axiom_overlap: not an AxiomOverlap goal: " goal
  end.

(* Tactic to prove spec overlap *)
Ltac prove_spec_overlap :=
  lazymatch goal with
    | |- SpecOverlap (Spec_Cons ?f1 ?T1 ?oppred1 ?rest1)
                     (Spec_Cons ?f2 ?T2 ?oppred2 ?rest2) =>
      lazymatch eval hnf in (Field_dec f1 f2) with
        | left _ =>
          (apply SpecOverlap_eq
                 || fail "Non-matching types or predicates at op" f1
                         ": types: " T1 ", " T2
                         "; predicates: " oppred1 ", " oppred2);
          intros; prove_spec_overlap
        | right ?neq =>
          ((apply SpecOverlap_neq1; [ prove_not_in_spec | intros ]) ||
           (apply SpecOverlap_neq2; [ prove_not_in_spec | intros ]) ||
           fail "The fields " f1 " and " f2 " appear to be in a different order in the two specs");
          prove_spec_overlap
      end
    | |- SpecOverlap (Spec_Cons _ _ _ _) (Spec_Axioms _) =>
      apply SpecOverlap_neq1; [ apply NotInSpec_base | intros; prove_spec_overlap ]
    | |- SpecOverlap (Spec_Axioms _) (Spec_Cons _ _ _ _) =>
      apply SpecOverlap_neq2; [ apply NotInSpec_base | intros; prove_spec_overlap ]
    | |- SpecOverlap (Spec_Axioms _) (Spec_Axioms _) =>
      apply SpecOverlap_base; prove_axiom_overlap
    | |- SpecOverlap ?spec1 ?spec2 =>
      let spec1_hnf := (eval hnf in spec1) in
      let spec2_hnf := (eval hnf in spec2) in
      progress (change (SpecOverlap spec1_hnf spec2_hnf)); prove_spec_overlap
    | |- ?goal => fail "prove_spec_overlap: not a SpecOverlap goal: " goal
  end.

(* Debugging version of the above tactic to prove spec overlap *)
Ltac prove_spec_overlapN n :=
  lazymatch n with
    | 0 => idtac "prove_spec_overlapN: n exhausted"
    | S ?n' =>
      lazymatch goal with
        | |- SpecOverlap (Spec_Cons ?f1 ?T1 ?oppred1 ?rest1)
                         (Spec_Cons ?f2 ?T2 ?oppred2 ?rest2) =>
          idtac "prove_spec_overlapN: cons-cons";
          lazymatch eval hnf in (Field_dec f1 f2) with
            | left _ =>
              (apply SpecOverlap_eq
                     || fail "Non-matching types or predicates at op" f1
                             ": types: " T1 ", " T2
                             "; predicates: " oppred1 ", " oppred2);
              intros; prove_spec_overlapN n'
            | right ?neq =>
              ((apply SpecOverlap_neq1; [ prove_not_in_spec | intros ]) ||
               (apply SpecOverlap_neq2; [ prove_not_in_spec | intros ]) ||
               fail "The fields " f1 " and " f2 " appear to be in a different order in the two specs");
              prove_spec_overlapN n'
          end
        | |- SpecOverlap (Spec_Cons _ _ _ _) (Spec_Axioms _) =>
          idtac "prove_spec_overlapN: cons-axiom";
          apply SpecOverlap_neq1; [ apply NotInSpec_base | intros; prove_spec_overlapN n' ]
        | |- SpecOverlap (Spec_Axioms _) (Spec_Cons _ _ _ _) =>
          idtac "prove_spec_overlapN: axiom-cons";
          apply SpecOverlap_neq2; [ apply NotInSpec_base | intros; prove_spec_overlapN n' ]
        | |- SpecOverlap (Spec_Axioms _) (Spec_Axioms _) =>
          idtac "prove_spec_overlapN: axiom-axiom";
          apply SpecOverlap_base; prove_axiom_overlap
        | |- SpecOverlap ?spec1 ?spec2 =>
          idtac "prove_spec_overlapN: hnf";
          let spec1_hnf := (eval hnf in spec1) in
          let spec2_hnf := (eval hnf in spec2) in
          progress (change (SpecOverlap spec1_hnf spec2_hnf)); prove_spec_overlapN n'
        | |- ?goal => fail "prove_spec_overlapN: not a SpecOverlap goal: " goal
      end
  end.


(*** Spec Substitution ***)

(* Helper for spec_subtract: return all axioms in the axioms1 list that do not
overlap with the axioms in axioms2 *)
Fixpoint axioms_subtract axioms1 axioms2
         (overlap: AxiomOverlap axioms1 axioms2) : list SpecAxiom :=
  match overlap with
    | AxiomOverlap_base => []
    | AxiomOverlap_eq ax_name ax_tp axioms1 axioms2 overlap' =>
      axioms_subtract axioms1 axioms2 overlap'
    | AxiomOverlap_neq1 ax_name ax_tp axioms1' axioms2' not_in overlap' =>
      (specAxiom ax_name ax_tp)
        :: axioms_subtract axioms1' axioms2' overlap'
    | AxiomOverlap_neq2 ax_name ax_tp axioms1' axioms2' not_in overlap' =>
      axioms_subtract axioms1' axioms2' overlap'
  end.

(* If you subtract axioms2 from axioms1 and then add them back again you can
prove the original axioms1. *)
Lemma axioms_subtract_interp axioms1 axioms2 overlap :
  conjoin_axioms axioms2 ->
  conjoin_axioms (axioms_subtract axioms1 axioms2 overlap) ->
  conjoin_axioms axioms1.
  induction overlap; intros.
  trivial.
  destruct (conjoin_axioms_destruct _ _ _ H).
  apply conjoin_axioms_cons; [ assumption | apply IHoverlap; assumption ].
  destruct (conjoin_axioms_destruct _ _ _ H0).
  apply conjoin_axioms_cons; [ assumption | apply IHoverlap; assumption ].
  destruct (conjoin_axioms_destruct _ _ _ H).
  apply IHoverlap; assumption.
Qed.

(* Subtract the overlapping ops and axioms in spec2 from spec1. Note that this
operation requires ops for spec2. *)
Fixpoint spec_subtract spec1 spec2 (overlap: SpecOverlap spec1 spec2) :
  spec_ops spec2 -> Spec :=
  match overlap in SpecOverlap spec1 spec2 return spec_ops spec2 -> Spec with
    | SpecOverlap_base axioms1 axioms2 overlap' =>
      fun _ => Spec_Axioms (axioms_subtract axioms1 axioms2 overlap')
    | SpecOverlap_eq f T oppred rest1 rest2 overlap' =>
      fun ops2 =>
        let (t,pf,ops2') := ops2 in
        spec_subtract (rest1 t pf) (rest2 t pf) (overlap' t pf) ops2'
    | SpecOverlap_neq1 f1 T1 oppred1 rest1 spec2 not_in overlap' =>
      fun ops2 =>
        Spec_Cons f1 T1 oppred1
                    (fun t pf =>
                       spec_subtract (rest1 t pf) spec2 (overlap' t pf) ops2)
    | SpecOverlap_neq2 f2 T2 oppred2 rest2 spec1 not_in overlap' =>
      fun ops2 =>
        let (t,pf,ops2') := ops2 in
        spec_subtract spec1 (rest2 t pf) (overlap' t pf) ops2'
  end.

(* If you subtract spec2 from spec1 then you can recover a model of spec1 if you
have models for spec2 and for the subtraction. This is like a binary
interpretation from spec1 to the pair (spec2, spec1-spec2). *)
Fixpoint interp_spec_subtract_model spec1 spec2 overlap :
  forall (model2:spec_model spec2),
  spec_model (spec_subtract spec1 spec2 overlap (extract_spec_ops model2)) ->
  spec_model spec1 :=
  match overlap in SpecOverlap spec1 spec2
        return forall model2,
                 spec_model (spec_subtract spec1 spec2 overlap
                                           (extract_spec_ops model2)) ->
                 spec_model spec1 with
    | SpecOverlap_base axioms1 axioms2 overlap' =>
      fun model2 model21 =>
        axioms_subtract_interp axioms1 axioms2 overlap' model2 model21
    | SpecOverlap_eq f T oppred rest1 rest2 overlap' =>
      fun model2 =>
        match model2 return
              spec_model (spec_subtract
                          _ _ (SpecOverlap_eq _ _ _ _ _ overlap')
                          (@extract_spec_ops
                             (Spec_Cons f T oppred rest2)
                             model2)) ->
              spec_model (Spec_Cons f T oppred rest1) with
          | opCons t pf model2' =>
            fun model21 =>
              opCons t pf (interp_spec_subtract_model _ _ (overlap' t pf)
                                                      model2' model21)
        end
    | SpecOverlap_neq1 f1 T1 oppred1 rest1 spec2 not_in overlap' =>
      fun model2 model21 =>
        match model21 return spec_model (Spec_Cons f1 T1 oppred1 rest1) with
          | opCons t pf model21' =>
            opCons t pf (interp_spec_subtract_model _ _ (overlap' t pf)
                                                    model2 model21')
        end
    | SpecOverlap_neq2 f2 T2 oppred2 rest2 spec1 not_in overlap' =>
      fun model2 =>
        match model2 return
              spec_model (spec_subtract
                          _ _ (SpecOverlap_neq2 _ _ _ _ _ _ overlap')
                          (@extract_spec_ops
                             (Spec_Cons f2 T2 oppred2 rest2)
                             model2)) ->
              spec_model spec1 with
          | opCons t pf model2' =>
            fun model21 =>
              interp_spec_subtract_model _ _ (overlap' t pf) model2' model21
        end
  end.

(* Same as interp_spec_subtract_model but for ops *)
Fixpoint interp_spec_subtract_ops spec1 spec2 overlap :
  forall (ops2:spec_ops spec2),
  spec_ops (spec_subtract spec1 spec2 overlap ops2) ->
  spec_ops spec1 :=
  match overlap in SpecOverlap spec1 spec2
        return forall ops2,
                 spec_ops (spec_subtract spec1 spec2 overlap ops2) ->
                 spec_ops spec1 with
    | SpecOverlap_base axioms1 axioms2 overlap' =>
      fun ops2 ops21 => tt
    | SpecOverlap_eq f T oppred rest1 rest2 overlap' =>
      fun ops2 =>
        match ops2 return
              spec_ops (spec_subtract
                          _ _ (SpecOverlap_eq _ _ _ _ _ overlap') ops2) ->
              spec_ops (Spec_Cons f T oppred rest1) with
          | opCons t pf ops2' =>
            fun ops21 =>
              opCons t pf (interp_spec_subtract_ops _ _ (overlap' t pf)
                                                    ops2' ops21)
        end
    | SpecOverlap_neq1 f1 T1 oppred1 rest1 spec2 not_in overlap' =>
      fun ops2 ops21 =>
        match ops21 return spec_ops (Spec_Cons f1 T1 oppred1 rest1) with
          | opCons t pf ops21' =>
            opCons t pf (interp_spec_subtract_ops _ _ (overlap' t pf)
                                                  ops2 ops21')
        end
    | SpecOverlap_neq2 f2 T2 oppred2 rest2 spec1 not_in overlap' =>
      fun ops2 =>
        match ops2 return
              spec_ops (spec_subtract
                          _ _ (SpecOverlap_neq2 _ _ _ _ _ _ overlap') ops2) ->
              spec_ops spec1 with
          | opCons t pf ops2' =>
            fun ops21 =>
              interp_spec_subtract_ops _ _ (overlap' t pf) ops2' ops21
        end
  end.

Lemma interp_spec_subtract_proof spec1 spec2 overlap :
  forall model2 model21,
    extract_spec_ops
      (interp_spec_subtract_model spec1 spec2 overlap model2 model21)
    = interp_spec_subtract_ops spec1 spec2 overlap (extract_spec_ops model2)
                               (extract_spec_ops model21).
  induction overlap; intros; admit.
Qed.


(* Build a spec using spec substitution *)
Definition spec_subst {spec spec1 spec2}
           (overlap: SpecOverlap spec spec1) (i: Interpretation spec1 spec2) : Spec :=
  spec_append spec2
              (fun ops2 =>
                 spec_subtract spec spec1 overlap (map_ops i ops2)).

(* FIXME HERE NOW: looks like doing the proof for interp_spec_subst1 is going to
require UIP, since the second argument of interp_spec_subtract_model is
dependent on the first, which needs to be cast using the interp_pf of i.

IDEA: maybe this could work via induction on spec2 followed by induction on
spec1, so that the interp_pf is used to cast each op separately instead of for
the whole spec substitution. The latter induction, on spec1, would be a version
of interp_spec_subtract_model that also takes i as an argument. *)

Definition interp_spec_subst1_model spec spec1 spec2 overlap i :
  spec_model (@spec_subst spec spec1 spec2 overlap i) ->
  spec_model spec.
  revert spec spec1 overlap i; induction spec2; unfold spec_subst; intros.
  apply (interp_spec_subtract_model
           _ _ overlap (map_model i (map_model (interp_append1 _ _) X))).
  rewrite (get_interp_pf i).
  rewrite (get_interp_pf (interp_append1 _ _)).
  apply (interp_append2_model _ _ X).
  destruct X0 as [t pf model'].
  refine (X t pf _ _ overlap
            (mkInterp (fun model =>
                         map_model i (opCons (U:=fun t pf => spec_model (rest t pf)) t pf model))
                      (fun ops =>
                         map_ops i (opCons (U:=fun t pf => spec_ops (rest t pf)) t pf ops)) _)
            model').
  intro; apply (get_interp_pf i).
Defined.

Print interp_spec_subst1_model.

Definition interp_spec_subst1_ops spec spec1 spec2 overlap i :
  spec_ops (@spec_subst spec spec1 spec2 overlap i) ->
  spec_ops spec.
  revert spec spec1 overlap i; induction spec2; unfold spec_subst; intros.
  apply (interp_spec_subtract_ops
           _ _ overlap (map_ops i (map_ops (interp_append1 _ _) X))).
  apply (interp_append2_ops _ _ X).
  destruct X0 as [t pf ops'].
  refine (X t pf _ _ overlap
            (mkInterp (fun model =>
                         map_model i (opCons (U:=fun t pf => spec_model (rest t pf)) t pf model))
                      (fun ops =>
                         map_ops i (opCons (U:=fun t pf => spec_ops (rest t pf)) t pf ops)) _)
            ops').
  intro; apply (get_interp_pf i).
Defined.



Program Definition interp_spec_subst1 spec spec1 spec2 overlap i :
  Interpretation spec (@spec_subst spec spec1 spec2 overlap i) :=
  mkInterp (interp_spec_subst1_model spec spec1 spec2 overlap i)
           (interp_spec_subst1_ops spec spec1 spec2 overlap i)
           _.
Obligation 1.
revert spec spec1 overlap i model2; induction spec2; intros.
*)


(* Build the interpretation from spec1 to the result of applying spec
substitution to spec1 *)
Program Definition spec_subst_interp1 {spec spec1 spec2} overlap i :
  Interpretation spec (@spec_subst spec spec1 spec2 overlap i) :=
  mkInterp
    (fun model =>
       interp_spec_subtract_model
         _ _ overlap
         (map_model i (map_model (interp_append1 _ _) model))
         (interp_append2_model _ _ model))
    (fun ops =>
       interp_spec_subtract_ops
         _ _ overlap
         (map_ops i (map_ops (interp_append1 _ _) ops))
         (interp_append2_ops _ _ ops))
    _.
Preterm.
Obligation 1.
f_equal.
rewrite (get_interp_pf i).
rewrite (get_interp_pf (interp_append1 spec2 _)).
reflexivity.
Defined.
Obligation 2.
rewrite interp_spec_subtract_proof.

induction spec2.

f_equal.
rewrite (get_interp_pf i (map_model (interp_append1 spec2 _ ) model2)).

re

fold (spec_subtract spec spec1 overlap).

  unfold spec_subst.
  eapply interp_append; intros.
  apply spec_subtract_interp_model.
  apply (map_model i _ H).
  apply H0.
Defined.

(* Build the interpretation from spec2 to the result of applying any spec
substitution using an interpretation into spec2 *)
Definition spec_subst_interp2 {spec spec1 spec2} overlap i :
  Interpretation spec2 (@spec_subst spec spec1 spec2 overlap i) :=
  interp_append1 _ _.


(*** Quantifying over the Ops of a Spec ***)

Definition ForallOp T (oppred: OpPred T) : (forall t, oppred t -> Type) -> Type :=
  match oppred return (forall t, sats_op_pred oppred t -> Type) -> Type with
    | Pred_Trivial => fun A => forall t, A t I
    | _ => fun A => forall t pf, A t pf
  end.

Definition LambdaOp T oppred : forall body_tp, (forall t pf, body_tp t pf) ->
                                               ForallOp T oppred body_tp :=
  match oppred return forall body_tp, (forall t pf, body_tp t pf) ->
                                      ForallOp T oppred body_tp with
    | Pred_Trivial => fun body_tp body => fun t => body t I
    | _ => fun body_tp body => fun t pf => body t pf
  end.

Definition replace_op_proof T (oppred: OpPred T) : forall t, oppred t -> oppred t :=
  match oppred return forall t, sats_op_pred oppred t ->
                                sats_op_pred oppred t with
    | Pred_Trivial => fun t _ => I
    | _ => fun t pf => pf
  end.

(* Helper: all proofs of True are equal *)
Definition True_eq (pf1: True) : forall pf2, pf1 = pf2 :=
  match pf1 return forall pf2, pf1 = pf2 with
    | I => fun pf2 => match pf2 return I = pf2 with I => eq_refl end end.

(* Helper: all elements of unit are equal *)
Definition unit_eq (u1: unit) : forall u2, u1 = u2 :=
  match u1 return forall u2, u1 = u2 with
    | tt => fun u2 => match u2 return tt = u2 with tt => eq_refl end end.
 
(* Replacing an op proof yields an equal proof (because a proof of True is a
proof of True) *)
Definition replace_op_proof_eq T (oppred: OpPred T) :
  forall t pf, pf = replace_op_proof T oppred t pf :=
  match oppred return forall t pf, pf = replace_op_proof T oppred t pf with
    | Pred_Trivial => fun t _ => True_eq _ _
    | _ => fun t pf => eq_refl
  end.

(* Apply an op function to an op and its proof *)
Definition ApplyOp T (oppred: OpPred T) :
  forall body_tp, ForallOp T oppred body_tp ->
                  forall t pf, body_tp t (replace_op_proof T oppred t pf) :=
  match oppred return forall body_tp,
                        ForallOp T oppred body_tp ->
                        forall t pf, body_tp t (replace_op_proof T oppred t pf) with
    | Pred_Trivial => fun body_tp body t pf => body t
    | _ => fun body_tp body t pf => body t pf
  end.

(* The type of Curried functions on the ops of spec *)
Fixpoint ForallOps spec : (spec_ops spec -> Type) -> Type :=
  match spec with
    | Spec_Axioms _ => fun body_tp => body_tp tt
    | Spec_Cons f T oppred rest =>
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
    | Spec_Cons f T oppred rest =>
      fun body_tp body =>
        LambdaOp T oppred _
                 (fun t pf =>
                    LambdaOps (rest t pf) _ (fun ops => body (ops_cons t pf ops)))
  end.

(* Replace all the trivial True proofs in a spec_ops with I *)
Fixpoint replace_op_proofs spec : spec_ops spec -> spec_ops spec :=
  match spec with
    | Spec_Axioms _ => fun ops => ops
    | Spec_Cons f T oppred rest =>
      fun ops =>
        ops_cons (ops_head ops)
                 (replace_op_proof T oppred _ (ops_proof ops))
                 (replace_op_proofs (rest _ _)
                                    (rew [fun pf => spec_ops (rest _ pf)]
                                         replace_op_proof_eq T oppred _ _
                                         in (ops_rest ops)))
  end.

(* Replacing all the trivial proofs yields an equal ops list *)
Lemma replace_op_proofs_eq spec ops : replace_op_proofs spec ops = ops.
  induction spec.
  reflexivity.
  unfold replace_op_proofs; fold replace_op_proofs.
  destruct ops as [t ops]; destruct ops as [pf ops].
  unfold ops_head; unfold ops_proof; unfold ops_rest; unfold ops_cons;
    unfold projT1; unfold projT2.
  destruct oppred; unfold replace_op_proof; unfold replace_op_proof_eq;
    rewrite H; unfold eq_rect;
    [ destruct pf | | ]; reflexivity.
Qed.

(* Apply a Curried predicate to some candidate ops for spec *)
Fixpoint ApplyOps spec : forall A, (ForallOps spec A) ->
                                   forall ops, A (replace_op_proofs spec ops) :=
  match spec return forall A, (ForallOps spec A) ->
                              forall ops, A (replace_op_proofs spec ops) with
    | Spec_Axioms _ =>
      fun A body ops => rew [A] (unit_eq _ _) in body
    | Spec_Cons f T oppred rest =>
      fun A body ops =>
        ApplyOps
          (rest (ops_head ops)
                (replace_op_proof T oppred _ (ops_proof ops)))
          (fun ops => A (ops_cons _ _ ops))
          (ApplyOp T oppred _ body (ops_head ops) (ops_proof ops))
          (rew [fun pf => spec_ops (rest _ pf)]
               replace_op_proof_eq T oppred _ _ in ops_rest ops)
  end.


(*** Types / Typeclasses Represented by Specs ***)

(* FIXME: remove IsoToSpec and IsoInterpretation, and possibly ForallOps *)

(* Whether P is isomorphic to spec *)
Class IsoToSpec spec (P: OpsPred spec) : Prop :=
  spec_iso: forall ops, ApplyOps spec _ P ops <-> spec_model spec ops.

(* An IsoInterpretation is an interpretation between type classes / type
functions that are isomorphic to specs *)
Definition IsoInterpretation {spec1 P1} (iso1: IsoToSpec spec1 P1)
           {spec2 P2} (iso2: IsoToSpec spec2 P2)
           (ops_f: spec_ops spec2 -> spec_ops spec1) : Type :=
  ForallOps spec2 (fun ops2 => ApplyOps spec2 _ P2 ops2 ->
                               ApplyOps spec1 _ P1 (ops_f ops2)).

(* Turn an interpretation from spec1 to spec2 into a function from a predicate
isomorphic to spec2 to a predicate ismorphic to spec1 *)
Definition toIsoInterp {spec1 P1} {iso1: IsoToSpec spec1 P1}
           {spec2 P2} {iso2: IsoToSpec spec2 P2}
           (i: Interpretation spec1 spec2) :
  IsoInterpretation iso1 iso2 (map_ops i) :=
  LambdaOps spec2 _ (fun ops2 p2 =>
                       proj2 (spec_iso (map_ops i ops2))
                             (map_model i ops2 (proj1 (spec_iso ops2) p2))).

(* Turn an IsoInterpretation into an Interpretation *)
Definition fromIsoInterp {spec1 P1} {iso1: IsoToSpec spec1 P1}
           {spec2 P2} {iso2: IsoToSpec spec2 P2} {ops_f}
           (i: IsoInterpretation iso1 iso2 ops_f) :
  Interpretation spec1 spec2 :=
  mkInterp ops_f (fun ops2 model2 =>
                    proj1 (spec_iso (ops_f ops2))
                          (rew [fun ops => ApplyOps spec1 _ P1 (ops_f ops)]
                               (replace_op_proofs_eq _ _)
                            in ApplyOps _ _ i ops2
                                        (rew [ApplyOps spec2 _ P2]
                                             (eq_sym (replace_op_proofs_eq _ _))
                                          in proj2 (spec_iso ops2) model2))).


(*** Examples of Isomorphic Interpretations ***)

(* Tactic to prove IsoToSpec instances *)
Ltac prove_spec_iso :=
  intro ops;
  repeat (let t := fresh "t" in
          let pf := fresh "pf" in
          destruct ops as [t ops]; destruct ops as [pf ops];
          try destruct pf);
  destruct ops; split; compute;
  [ intro H; destruct H;
    repeat (first [ assumption | split; [assumption|] | apply I])
  | intro H; repeat (let Hi := fresh "H" in
                     destruct H as [Hi H]); constructor; assumption ].

(* Example 1:  op n:nat;  axiom gt1: n > 1 *)
Class spec_example_1_class (n:nat) : Prop :=
  { example_1__gt1 : n > 1 }.

(* Isomorphism between spec_example_1 and spec_example_1_class *)
Instance iso_example_1 : IsoToSpec spec_example_1 spec_example_1_class.
prove_spec_iso.
Qed.

(* Example 2:  op n:nat := 2;  (no axioms) *)
Class spec_example_2_class (n:nat) (n__pf: n = 2) : Prop := { }.

Instance iso_example_2 : IsoToSpec spec_example_2 spec_example_2_class.
prove_spec_iso.
Qed.

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Class spec_example_3_class (T:Set) (T__pf: T = nat) (n: def T T__pf) : Prop :=
  { example_3__gt1 : n > 1 }.

Instance iso_example_3 : IsoToSpec spec_example_3 spec_example_3_class.
prove_spec_iso.
Qed.

(* Example: lift the spec3 -> spec2 interpretation to an instance function *)
Instance iso_interp_example_3_2 : forall `{spec_example_2_class}, spec_example_3_class _ _ _ :=
  toIsoInterp (interp_example_3_2).

(* Example 4: monoids *)
Class Monoid {T:Set} {m_zero:T} {m_plus:T -> T -> T} : Prop :=
  {m_zero_left : (forall x, m_plus m_zero x = x);
   m_zero_right : (forall x, m_plus x m_zero = x);
   m_plus_assoc : (forall x y z, m_plus x (m_plus y z) = m_plus (m_plus x y) z)}.

Instance iso_example_monoid : IsoToSpec spec_example_monoid (@Monoid).
prove_spec_iso.
Qed.

(* Example 4: groups *)
Class Group {T:Set} {g_zero:T} {g_plus:T -> T -> T} {g_inv:T -> T} : Prop :=
  {g_zero_left : (forall x, g_plus g_zero x = x);
   g_zero_right : (forall x, g_plus x g_zero = x);
   g_plus_assoc : (forall x y z, g_plus x (g_plus y z) = g_plus (g_plus x y) z);
   g_inv_left : (forall (x:T), g_plus (g_inv x) x = g_zero);
   g_inv_right : (forall (x:T), g_plus x (g_inv x) = g_zero)}.

Instance iso_example_group : IsoToSpec spec_example_group (@Group).
prove_spec_iso.
Qed.

(* Interpretation from Monoid to Group type classes *)
Program Instance group_as_monoid `{Group} :
  Monoid (m_zero:=g_zero) (m_plus:=g_plus).
Next Obligation. apply g_zero_left. Qed.
Next Obligation. apply g_zero_right. Qed.
Next Obligation. apply g_plus_assoc. Qed.

(*
NOTE: the below loops forever!

Check (@group_as_monoid : IsoInterpretation iso_example_monoid iso_example_group _).
Check (fromIsoInterp (iso1:=iso_example_monoid)
                     (iso2:=iso_example_group)
                     (@group_as_monoid)).
*)


(*** An Alternative Isomorphism to Specs ***)

Class IsoToSpecModels {spec} (ops: spec_ops spec) (P: Prop) : Prop :=
  spec_models_iso : P <-> spec_model spec ops.

(* Tactic to prove IsoToSpec instances *)
Ltac prove_spec_models_iso :=
  split; compute;
  [ intro H; destruct H;
    repeat (first [ assumption | split; [assumption|] | apply I])
  | intro H; repeat (let Hi := fresh "H" in
                     destruct H as [Hi H]); constructor; assumption ].


(*** Spec Translations ***)

(* A spec translation element, which denotes either a single mapping from field
f_from to field f_to, or a set of mappings from fields with prefix f_from_prefix
to the result of replacing that prefix with f_to_prefix. *)
Inductive SpecTranslationElem : Set :=
| XlateSingle (f_from f_to : Field)
| XlatePrefix (f_from_prefix f_to_prefix : string)
.

Arguments XlateSingle (f_from%string) (f_to%string).
Arguments XlatePrefix (f_from_prefix%string) (f_to_prefix%string).

(* A spec translation is just a list of spec translation elements *)
Inductive SpecTranslation : Set :=
| mkSpecTranslation (elems: list SpecTranslationElem).

Notation "f_from '+->' f_to" :=
  (XlateSingle f_from f_to)
  (at level 80, no associativity) : spec_translation_elem_scope.
Notation "f_from '%' '+->' f_to '%'" :=
  (XlatePrefix f_from f_to)
  (at level 80, no associativity) : spec_translation_elem_scope.

Bind Scope spec_translation_elem_scope with SpecTranslationElem.
Delimit Scope spec_translation_elem_scope with spec_translation_elem.

(* We use double curly brackets to write spec translations *)
Notation "'{' elem1 , .. , elemn '}'" :=
  (mkSpecTranslation (cons elem1%spec_translation_elem .. (cons elemn%spec_translation_elem nil) ..))
  (at level 0) : spec_translation_scope.
Notation "'{' '}'" :=
  (mkSpecTranslation nil)
  (at level 0) : spec_translation_scope.

Bind Scope spec_translation_scope with SpecTranslation.
Delimit Scope spec_translation_scope with spec_translation.

Definition translate_field1 elem (f: Field) : option Field :=
  match elem with
    | XlateSingle f_from f_to =>
      if Field_dec f f_from then Some f_to else None
    | XlatePrefix f_from_prefix f_to_prefix =>
      if Field_dec (substring 0 (length f_from_prefix) f) f_from_prefix then
        Some (append f_to_prefix (substring (length f_from_prefix)
                                            (length f - length f_from_prefix) f))
      else None
  end.

Definition translate_field xlate f : Field :=
  match xlate with
    | mkSpecTranslation elems =>
      fold_right (fun elem rec =>
                    match translate_field1 elem f with
                      | Some f' => f'
                      | None => rec
                    end) f elems
  end.

Definition translate_spec_axioms xlate axioms : list SpecAxiom :=
  map (fun ax =>
         match ax with
           | specAxiom f P => specAxiom (translate_field xlate f) P
         end) axioms.

Fixpoint translate_spec xlate spec : Spec :=
  match spec with
    | Spec_Axioms axioms =>
      Spec_Axioms (translate_spec_axioms xlate axioms)
    | Spec_Cons f T oppred rest =>
      Spec_Cons (translate_field xlate f) T oppred
                  (fun x x__pf => translate_spec xlate (rest x x__pf))
  end.

(* NOTE: the spec_ops type of a translated spec is in fact equal to that of the
original spec, but this requires functional extensionality to prove... *)

Fixpoint translate_spec_ops xlate spec :
  spec_ops (translate_spec xlate spec) -> spec_ops spec :=
  match spec return spec_ops (translate_spec xlate spec) -> spec_ops spec with
    | Spec_Axioms _ => fun ops => ops
    | Spec_Cons f T oppred rest =>
      fun ops =>
        match ops with
          | existT _ t_o (existT _ pf_o ops') =>
            ops_cons t_o pf_o (translate_spec_ops xlate _ ops')
        end
  end.

Lemma translate_spec_axioms_impl xlate axioms :
  conjoin_axioms (translate_spec_axioms xlate axioms) -> conjoin_axioms axioms.
  induction axioms.
  intro; assumption.
  destruct axioms; destruct a.
  intro; assumption.
  intro H; destruct H; split.
  assumption.
  apply IHaxioms; assumption.
Defined.

(* Build an interpretation from spec to (translate_spec xlate spec) *)
Program Definition interp_translate_spec xlate spec :
  Interpretation spec (translate_spec xlate spec) :=
  mkInterp (translate_spec_ops xlate spec) _.
Next Obligation.
revert ops H; induction spec; intros.
apply (translate_spec_axioms_impl xlate); assumption.
destruct ops as [t_o ops]; destruct ops as [pf_o ops].
apply H. assumption.
Defined.

(* Reverse the translation of spec ops *)
Fixpoint untranslate_spec_ops xlate spec :
  spec_ops spec -> spec_ops (translate_spec xlate spec) :=
  match spec return spec_ops spec -> spec_ops (translate_spec xlate spec) with
    | Spec_Axioms _ => fun ops => ops
    | Spec_Cons f T oppred rest =>
      fun ops =>
        match ops with
          | existT _ t_o (existT _ pf_o ops') =>
            ops_cons t_o pf_o (untranslate_spec_ops xlate _ ops')
        end
  end.

Lemma untranslate_spec_axioms_impl xlate axioms :
  conjoin_axioms axioms -> conjoin_axioms (translate_spec_axioms xlate axioms).
  induction axioms.
  intro; assumption.
  destruct axioms; destruct a.
  intro; assumption.
  intro H; destruct H; split.
  assumption.
  apply IHaxioms; assumption.
Defined.

(* Build an interpretation from (translate_spec xlate spec) back to spec *)
Program Definition interp_untranslate_spec xlate spec :
  Interpretation (translate_spec xlate spec) spec :=
  mkInterp (untranslate_spec_ops xlate spec) _.
Next Obligation.
revert ops H; induction spec; intros.
apply (untranslate_spec_axioms_impl xlate); assumption.
destruct ops as [t_o ops]; destruct ops as [pf_o ops].
apply H. assumption.
Defined.

(* Translate an interpretation *)
Definition translate_interp {spec1 spec2} xlate
           (i: Interpretation spec1 spec2) :
  Interpretation (translate_spec xlate spec1) (translate_spec xlate spec2) :=
  interp_compose (interp_translate_spec xlate spec2)
                 (interp_compose i (interp_untranslate_spec xlate spec1)).


(***
 *** Building Interprations using Translations
 ***)

(* Like interp_cons, but allow the head op name to be translated and the head op
predicate to be strengthened *)
Definition interp_cons_strengthen_xlate xlate f1 T (oppred1 oppred2: OpPred T)
           {spec1 spec2}
           (impl: forall t, oppred2 t -> oppred1 t)
           (i: forall t pf2,
                 Interpretation (spec1 t (impl t pf2)) (spec2 t pf2)) :
  Interpretation (Spec_Cons f1 T oppred1 spec1)
                 (Spec_Cons (translate_field xlate f1) T oppred2 spec2) :=
  mkInterp (fun ops2:spec_ops (Spec_Cons (translate_field xlate f1)
                                           T oppred2 spec2) =>
              let (t_o,o) := ops2 in
              let (pf_o, rest_o) := o in
              ops_cons t_o (impl _ pf_o) (map_ops (i t_o pf_o) rest_o))
           (fun ops2 =>
              match ops2
                    return spec_model (Spec_Cons (translate_field xlate f1)
                                                   T oppred2 spec2) ops2 ->
                           spec_model
                             (Spec_Cons f1 T oppred1 spec1)
                             (let (t_o,o) := ops2 in
                              let (pf_o,rest_o) := o in
                              ops_cons t_o (impl t_o pf_o) (map_ops (i _ _) rest_o)) with
                | existT _ t_o (existT _ pf_o rest_o) =>
                  fun model2 =>
                    map_model (i t_o pf_o) rest_o model2
              end).

(* Similar to the above, but substitute the definition of an op that is defined
in the co-domain into the domain spec *)
Definition interp_cons_def_xlate xlate f1 T (oppred1: OpPred T) t2
           {spec1: forall t, oppred1 t -> Spec} {spec2}
           (oppred1_pf: oppred1 t2)
           (i: forall t pf2,
                 Interpretation (spec1 t2 oppred1_pf) (spec2 t pf2)) :
  Interpretation (Spec_Cons f1 T oppred1 spec1)
                 (Spec_Cons (translate_field xlate f1) T (Pred_Eq t2) spec2) :=
  mkInterp (fun ops2:spec_ops (Spec_Cons (translate_field xlate f1)
                                           T (Pred_Eq t2) spec2) =>
              let (t_o,o) := ops2 in
              let (pf_o, rest_o) := o in
              ops_cons t2 oppred1_pf (map_ops (i t_o pf_o) rest_o))
           (fun ops2 =>
              match ops2
                    return spec_model (Spec_Cons (translate_field xlate f1)
                                                   T (Pred_Eq t2) spec2) ops2 ->
                           spec_model
                             (Spec_Cons f1 T oppred1 spec1)
                             (let (t_o,o) := ops2 in
                              let (pf_o,rest_o) := o in
                              ops_cons t2 oppred1_pf (map_ops (i _ _) rest_o)) with
                | existT _ t_o (existT _ pf_o rest_o) =>
                  fun model2 =>
                    map_model (i t_o pf_o) rest_o model2
              end).

(* Similar to the above, but allow the field types to be provably, not just
definitionally, equal *)
Definition interp_cons_strengthen_xlate_eq xlate f1 T1 T2 (oppred1: OpPred T1)
           (oppred2: OpPred T2)
           {spec1: forall t, oppred1 t -> Spec} {spec2}
           (eT: T2 = T1) (impl: forall t, oppred2 t -> oppred1 (rew eT in t))
           (i: forall t pf2,
                 Interpretation (spec1 (rew eT in t) (impl t pf2)) (spec2 t pf2)) :
  Interpretation (Spec_Cons f1 T1 oppred1 spec1)
                 (Spec_Cons (translate_field xlate f1) T2 oppred2 spec2) :=
  mkInterp (fun ops2:spec_ops (Spec_Cons (translate_field xlate f1)
                                           T2 oppred2 spec2) =>
              let (t_o,o) := ops2 in
              let (pf_o, rest_o) := o in
              ops_cons (rew eT in t_o) (impl _ pf_o) (map_ops (i t_o pf_o) rest_o))
           (fun ops2 =>
              match ops2
                    return spec_model (Spec_Cons (translate_field xlate f1)
                                                   T2 oppred2 spec2) ops2 ->
                           spec_model
                             (Spec_Cons f1 T1 oppred1 spec1)
                             (let (t_o,o) := ops2 in
                              let (pf_o,rest_o) := o in
                              ops_cons (rew eT in t_o) (impl t_o pf_o) (map_ops (i _ _) rest_o)) with
                | existT _ t_o (existT _ pf_o rest_o) =>
                  fun model2 =>
                    map_model (i t_o pf_o) rest_o model2
              end).

(* Tactic to prove a "simple" interpretation, which is one where none of the ops
have to be re-ordered, but where the fields can be translated between the domain
spec and the co-domain spec. *)
Ltac try_prove_simple_interp_pred :=
  try assumption; try apply I.
Ltac intros_for_cons_op f oppred :=
  (* FIXME: wish I could convert f to an id... *)
  let f_var := fresh "t" in
  let f_pf_var := fresh "pf" in
  intros f_var f_pf_var;
  (* (lazymatch oppred with
     | Pred_Eq _ =>
       rewrite f_pf_var
     | _ => idtac
   end) *)
  idtac.
Ltac prove_simple_interp xlate :=
  let next :=
      lazymatch goal with
      | |- Interpretation (Spec_Cons ?f1 ?T1 ?oppred1 ?rest1)
                          (Spec_Cons ?f2 ?T2 ?oppred2 ?rest2) =>
        lazymatch (eval cbn in (Field_dec f2 (translate_field xlate f1))) with
          | left _ =>
            first
              [ apply (interp_cons_def_xlate xlate);
                [ intros; try_prove_simple_interp_pred
                | intros_for_cons_op f2 oppred2; prove_simple_interp xlate ]
              | apply (interp_cons_strengthen_xlate xlate);
                [ intros; try_prove_simple_interp_pred
                | intros_for_cons_op f2 oppred2; prove_simple_interp xlate ]
              | (eapply (interp_cons_strengthen_xlate_eq
                           xlate f1 T1 T2 oppred1 oppred2);
                 [ intros; try_prove_simple_interp_pred
                 | intros_for_cons_op f2 oppred2; prove_simple_interp xlate ]) ]
          | right _ =>
            apply interp_cons_r; intros; prove_simple_interp xlate
        end
      | |- Interpretation (Spec_Axioms _)
                          (Spec_Cons ?f2 ?T2 ?oppred2 ?rest2) =>
        apply interp_cons_r; intros_for_cons_op f2 oppred2;
        prove_simple_interp xlate
      | |- Interpretation (Spec_Axioms _) (Spec_Axioms _) =>
        idtac "axioms";
        apply (mkInterp (fun _ => tt : spec_ops (Spec_Axioms _)));
        intros ops model; unfold spec_model, conjoin_axioms in model;
        repeat (let ax_name := fresh "axiom" in
                first [ destruct model as [ax_name model]
                      | rename model into ax_name ]);
        unfold spec_model, conjoin_axioms; repeat split;
        try assumption
      | |- Interpretation ?S1 ?S2 =>
        let S1' := (eval hnf in S1) in
        let S2' := (eval hnf in S2) in
        (progress (change S1 with S1'; change S2 with S2');
         prove_simple_interp xlate)
          || (* fail *) idtac "Cannot prove this interpretation!"
      end
    in
      next
.

(* Old version *)
(*
Ltac prove_simple_interp xlate :=
  repeat (first [apply (interp_cons_strengthen_xlate xlate);
                  intros; [ try assumption | ]
                | apply interp_cons_r; intros ]);
  apply (mkInterp (fun _ => tt : spec_ops (Spec_Axioms _))); intros ops model;
  unfold spec_model, conjoin_axioms, specAxiom, snd in model;
  repeat (let ax_name := fresh "axiom" in
          first [ destruct model as [ax_name model] | rename model into ax_name ]);
  unfold spec_model, conjoin_axioms, specAxiom, snd; repeat split;
  try assumption.
*)


(* For proving the model part of an interpretation given by an interp_map *)
Ltac interp_tactic :=
  intros;
  lazymatch goal with
    | |- spec_model ?dom_spec (let (rest, t) := ?ops in ?body) =>
      destruct ops as [t ops]
    | |- Pred_Trivial _ => apply I
    | |- Pred_Fun _ => try assumption
    | |- _ => try (apply I); try assumption
  end.


(*** Refinement ***)

(* Helper wrapper around the refine tactic *)
Ltac specware_refine arg := refine arg.

(* A refinement import into spec is some spec', an interpretation from spec' to
spec, and a type that is isomorphic to spec' *)
Record RefinementImport spec : Type :=
  {ref_import_fromspec: Spec;
   ref_import_interp: Interpretation ref_import_fromspec spec}.

(* A refinement of spec is some ref_spec, an interpretation from spec to
ref_spec, and a list of refinement imports for ref_spec *)
Record RefinementOf spec : Type :=
  {ref_spec: Spec;
   ref_interp: Interpretation spec ref_spec;
   ref_imports: list (RefinementImport ref_spec)}.

(* The identity refinement of a spec to itself, with no other specs *)
Definition id_refinement_noimport spec : RefinementOf spec :=
  {| ref_spec := spec;
     ref_interp := interp_id spec;
     ref_imports := [] |}.

(* Add a refinement import to a refinement *)
Definition refinement_add_import {spec} (R: RefinementOf spec) :
  RefinementImport (ref_spec _ R) -> RefinementOf spec :=
  match R as R return RefinementImport (ref_spec _ R) -> RefinementOf spec with
    | Build_RefinementOf _ s i imps =>
      fun (imp:RefinementImport s) => Build_RefinementOf _ s i (imp::imps)
  end.

(* Get the nth import of a RefinementOf, returning the identity if n is too big *)
Definition nth_refinement_import {spec} (R: RefinementOf spec) n :
  n < List.length (ref_imports _ R) -> RefinementImport (ref_spec _ R) :=
  nth_nodef n (ref_imports _ R).

(* The identity refinement with an import *)
Definition id_refinement spec : RefinementOf spec :=
  {| ref_spec := spec;
     ref_interp := interp_id spec;
     ref_imports := [ {| ref_import_fromspec := spec;
                           ref_import_interp := interp_id spec |} ] |}.

(* Compose an interpretation with a refinement import *)
Definition refinement_import_interp {spec spec'}
           (imp: RefinementImport spec)
           (i: Interpretation spec spec') : RefinementImport spec' :=
  match imp with
    | Build_RefinementImport _ fromspec interp =>
      Build_RefinementImport _ fromspec (interp_compose i interp)
  end.

(* Compose an interpretation with a refinement *)
Definition refinement_interp {spec spec'}
           (R: RefinementOf spec) :
  Interpretation (ref_spec _ R) spec' -> RefinementOf spec :=
  match R as R return Interpretation (ref_spec _ R) spec' ->
                      RefinementOf spec with
    | Build_RefinementOf _ s interp imps =>
      fun (i:Interpretation s spec') =>
        Build_RefinementOf _ spec' (interp_compose i interp)
                           (map (fun imp => refinement_import_interp imp i) imps)
  end.

(* Compose two refinements together *)
Definition refinement_compose {spec}
           (R1: RefinementOf spec) :
  RefinementOf (ref_spec spec R1) -> RefinementOf spec :=
  match R1 as R1 return RefinementOf (ref_spec spec R1) ->
                        RefinementOf spec with
    | Build_RefinementOf _ spec1 interp1 imps1 =>
      fun (R2: RefinementOf spec1) =>
        match R2 with
          | Build_RefinementOf _ spec2 interp2 imps2 =>
            {| ref_spec := spec2;
               ref_interp := interp_compose interp2 interp1;
               ref_imports :=
                 (map (fun imp => refinement_import_interp imp interp2) imps1)
                   ++ imps2 |}
        end
  end.

(* Apply a spec substitution to a refinement *)
Definition refinement_subst_noimport {spec spec1 spec2}
           (R: RefinementOf spec) (overlap: SpecOverlap (ref_spec _ R) spec1)
           (i: Interpretation spec1 spec2) : RefinementOf spec :=
  refinement_interp R (spec_subst_interp1 overlap i).

(* Apply a spec substitution to a refinement, importing the co-domain spec *)
Definition refinement_subst {spec spec1 spec2}
           (R: RefinementOf spec) (i: Interpretation spec1 spec2) :
  SpecOverlap (ref_spec _ R) spec1 -> RefinementOf spec :=
  match R as R return SpecOverlap (ref_spec _ R) spec1 -> RefinementOf spec with
    | Build_RefinementOf _ spec' interp imps =>
      fun (overlap: SpecOverlap spec' spec1) =>
        {| ref_spec := spec_subst overlap i;
           ref_interp := interp_compose (spec_subst_interp1 overlap i) interp;
           ref_imports :=
             {| ref_import_fromspec := spec2;
                ref_import_interp := spec_subst_interp2 overlap i |}
               ::(map (fun imp => refinement_import_interp
                                    imp (spec_subst_interp1 overlap i)) imps) |}
  end.

(* FIXME: document this *)
Definition spec_subst_interp2_xlate {spec1sub spec1 spec2}
           xlate (overlap: SpecOverlap spec1 (translate_spec xlate spec1sub))
           (i: Interpretation spec1sub spec2) :
  Interpretation spec2 (spec_subst overlap (translate_interp xlate i)) :=
 interp_compose (interp_append1 _ _) (interp_translate_spec _ _).

(* Apply a spec substitution to a refinement, using the translation of an
interpretation, importing the un-translated co-domain of the interpretation *)
Definition refinement_subst_xlate {spec spec1 spec2}
           (R: RefinementOf spec) (i: Interpretation spec1 spec2) xlate :
  SpecOverlap (ref_spec _ R) (translate_spec xlate spec1) -> RefinementOf spec :=
  match R as R return SpecOverlap (ref_spec _ R) (translate_spec xlate spec1) ->
                      RefinementOf spec with
    | Build_RefinementOf _ spec' interp imps =>
      fun (overlap: SpecOverlap spec' (translate_spec xlate spec1)) =>
        {| ref_spec := spec_subst overlap (translate_interp xlate i);
           ref_interp :=
             interp_compose (spec_subst_interp1
                               overlap (translate_interp xlate i)) interp;
           ref_imports :=
             {| ref_import_fromspec := spec2;
                ref_import_interp := spec_subst_interp2_xlate xlate overlap i |}
               ::(map (fun imp => refinement_import_interp
                                    imp (spec_subst_interp1
                                           overlap (translate_interp xlate i))) imps) |}
  end.

(* Translate a refinement *)
Definition refinement_translate {spec}
           (R: RefinementOf spec) xlate : RefinementOf spec :=
  refinement_interp R (interp_translate_spec xlate _).
