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
| Spec_Cons (f:Field) (T : Type) (rest : T -> Spec) : Spec
.

(* Make the field argument be parsed by Coq as a string *)
Arguments Spec_Cons f%string T rest.

(* Get the value of a defined variable *)
Definition def {T x} (t:T) (t__pf: t = x) : T := x.


(*** Relationships with Record Types ***)

Fixpoint SpecAxiomsCtor (R:Type) (axioms:list SpecAxiom) : Type :=
  match axioms with
    | [] => R
    | (specAxiom _ P)::axioms' =>
      P -> SpecAxiomsCtor R axioms'
  end.

(* The type of a constructor of R using spec *)
Fixpoint SpecCtor (R:Type) (spec:Spec) : Type :=
  match spec with
    | Spec_Axioms axioms => SpecAxiomsCtor R axioms
    | Spec_Cons f T rest =>
      forall x, SpecCtor R (rest x)
  end.

(* The type of projections of R indexed by some earlier projections *)
Inductive SpecProjs (R params:Type) (projs : R -> params) : (params -> Spec) -> Type :=
| Projs_Nil : SpecProjs R params projs (fun _ => Spec_Axioms nil)
| Projs_ConsAx f (P: params -> Prop) axioms (proj_pf: forall r, P (projs r)) :
    SpecProjs R params projs (fun p => Spec_Axioms (axioms p)) ->
    SpecProjs R params projs
              (fun p => Spec_Axioms (cons (specAxiom f (P p)) (axioms p)))
| Projs_Cons f T (rest: forall p:params, T p -> Spec)
             (proj: forall r, T (projs r)) :
    SpecProjs R {p:params & T p}
              (fun r => existT _ (projs r) (proj r))
              (fun p => rest (projT1 p) (projT2 p)) ->
    SpecProjs R params projs (fun p => Spec_Cons f (T p) (rest p))
.

Definition SpecProjsTop R spec :=
  SpecProjs R unit (fun _ => tt) (fun _ => spec).

Fixpoint nth_spec_proj_type {R params projs spec}
         (sprojs: SpecProjs R params projs spec) n (r:R) : Type :=
  match sprojs with
    | Projs_Nil _ _ _ => unit
    | Projs_ConsAx _ _ _ f P axioms proj_pf projs_rest =>
      match n with
        | 0 => P (projs r)
        | S n' => nth_spec_proj_type projs_rest n' r
      end
    | Projs_Cons _ _ _ f T rest proj projs_rest =>
      match n with
        | 0 => T (projs r)
        | S n' => nth_spec_proj_type projs_rest n' r
      end
  end.

Fixpoint nth_spec_proj {R params projs spec}
         (sprojs: SpecProjs R params projs spec) :
  forall n r, nth_spec_proj_type sprojs n r :=
  match sprojs return forall n r, nth_spec_proj_type sprojs n r with
    | Projs_Nil _ _ _ => fun _ _ => tt
    | Projs_ConsAx _ _ _ f P axioms proj_pf projs_rest =>
      fun n =>
        match n return forall r, nth_spec_proj_type (Projs_ConsAx _ _ _ _ _ _ _ _) n r with
          | 0 => proj_pf
          | S n' => nth_spec_proj projs_rest n'
        end
    | Projs_Cons _ _ _ f T rest proj projs_rest =>
      fun n =>
        match n return forall r, nth_spec_proj_type (Projs_Cons _ _ _ _ _ _ _ _) n r with
          | 0 => proj
          | S n' => nth_spec_proj projs_rest n'
        end
  end.


(* Examples *)

Record R1 : Type := { R1_n:nat; R1_m:nat; R1_lt_n_m:R1_n < R1_m }.

Definition R1_Spec :=
  Spec_Cons "n" nat
            (fun n =>
               Spec_Cons "m" nat
                         (fun m => Spec_Axioms [specAxiom "lt_n_m" (n < m)])).

Definition R1_ctor : SpecCtor R1 R1_Spec := Build_R1.

Definition R1_projs : SpecProjsTop R1 R1_Spec :=
  Projs_Cons
    _ _ _ _ _ _
    R1_n
    (Projs_Cons
       _ _ _ _ _ _
       R1_m
       (Projs_ConsAx _ _ _ _ _ _ R1_lt_n_m (Projs_Nil _ _ _))).

Class R2_class (R2_n R2_m : nat) : Prop :=
  {R2_lt_n_m: R2_n < R2_m;
   R2_lt_0_n: 0 < R2_n }.

Record R2 : Type := { R2_n:nat; R2_m:nat; R2_proofs:R2_class R2_n R2_m }.

Definition R2_Spec :=
  Spec_Cons "n" nat
            (fun n =>
               Spec_Cons "m" nat
                         (fun m =>
                            Spec_Axioms [specAxiom "lt_n_m" (n < m);
                                          specAxiom "lt_0_n" (0 < n)])).

Definition R2_ctor : SpecCtor R2 R2_Spec :=
  fun n m pf1 pf2 => Build_R2 n m (Build_R2_class n m pf1 pf2).

Set Printing All.

Definition R2_projs : SpecProjsTop R2 R2_Spec :=
  Projs_Cons
    _ _ _ _ _ _
    R2_n
    (Projs_Cons
       _ _ _ _ _ _
       R2_m
       (Projs_ConsAx
          _ _ _ _ _ _
          (fun r => @R2_lt_n_m (R2_n r) (R2_m r) (R2_proofs r))
          (Projs_ConsAx
             _ {x1:{_:unit & nat} & nat} _ _ _ _
             (fun r => @R2_lt_0_n (R2_n r) (R2_m r) (R2_proofs r))
             (Projs_Nil _ _ _)))).



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

(* Build the type of the models of spec as a nested dependent pair *)
Fixpoint spec_model spec : Type :=
  match spec with
    | Spec_Axioms axioms => conjoin_axioms axioms
    | Spec_Cons f T rest =>
      { t:T & spec_model (rest t) }
  end.

(* Project the first op of a spec *)
Definition model_head {f T rest}
           (model: spec_model (Spec_Cons f T rest)) : T :=
  match model with
    | existT _ t model' => t
  end.

(* Project the tail of the model of a spec *)
Definition model_rest {f T rest}
           (model: spec_model (Spec_Cons f T rest)) :
  spec_model (rest (model_head model)) :=
  match model with
    | existT _ t model' => model'
  end.


(*** Spec Examples ***)

(* Example 1:  op n:nat;  axiom gt1: n > 1 *)
Definition spec_example_1 :=
  Spec_Cons "n" nat
            (fun n => Spec_Axioms [specAxiom "gt1" (n > 1)]).

(* Example 2:  op n:nat := 2;  (no axioms) *)
Definition spec_example_2 :=
  Spec_Cons "n" nat
            (fun n =>
               Spec_Cons "n__proof" (n = 2)
                         (fun _ => Spec_Axioms [])).

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Definition spec_example_3 :=
  Spec_Cons
    "T__var" Set
    (fun T__var =>
       Spec_Cons
         "T__proof" (T__var = nat)
         (fun T__proof =>
            Spec_Cons "n" (def T__var T__proof)
                   (fun n => Spec_Axioms [specAxiom "gt1" (n > 1)]))).

(* Example 4: Monoids *)
Definition spec_example_monoid :=
  Spec_Cons
    "T" Set
    (fun T =>
       Spec_Cons
         "m_zero" T
         (fun m_zero =>
            Spec_Cons
              "m_plus" (T -> T -> T)
              (fun m_plus =>
                 Spec_Axioms
                   [specAxiom "m_zero_left" (forall x, m_plus m_zero x = x);
                     specAxiom "m_zero_right" (forall x, m_plus x m_zero = x);
                     specAxiom "m_plus_assoc"
                             (forall x y z,
                                m_plus x (m_plus y z) = m_plus (m_plus x y) z)]))).

(* Example 5: Groups *)
Definition spec_example_group :=
  Spec_Cons
    "T" Set
    (fun T =>
       Spec_Cons
         "g_zero" T
         (fun g_zero =>
            Spec_Cons
              "g_plus" (T -> T -> T)
              (fun g_plus =>
                 Spec_Cons
                   "g_inv" (T -> T)
                   (fun g_inv =>
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
Spec_Cons
  "T__var" Type
  (fun T__var =>
     Spec_Cons
       "T__proof" (T__var = nat)
       (fun T__proof =>
          let T := def T__var T__proof in
          Spec_Cons
            "m_zero" T
            (fun m_zero__var =>
               Spec_Cons
                 "m_zero__proof" (m_zero__var = 0)
                 (fun m_zero__proof =>
                    let m_zero := def m_zero__var m_zero__proof in
                    Spec_Cons
                      "m_plus" (T -> T -> T)
                      (fun m_plus__var =>
                         Spec_Cons
                           "m_plus__proof" (m_plus__var = plus)
                           (fun m_plus__proof =>
                              let m_plus := def m_plus__var m_plus__proof in
                              Spec_Axioms
                                [specAxiom
                                   "m_zero_left"
                                   (forall x : T, m_plus m_zero x = x);
                                  specAxiom
                                    "m_zero_right"
                                    (forall x : T, m_plus x m_zero = x);
                                  specAxiom
                                    "m_plus_assoc"
                                    (forall x y z : T,
                                       m_plus x (m_plus y z) =
                                       m_plus (m_plus x y) z)])))))).

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
  existT
    _ T__param
    (existT
       _ T__proof
       (existT
          _ m_zero__param
          (existT
             _ m_zero__proof
             (existT
                _ m_plus__param
                (existT
                   _ m_plus__proof
                   (conj m_zero_left__param
                         (conj m_zero_right__param m_plus_assoc__param))))))).


(*** Interpretations ***)

(* An interpretation from spec1 into spec2 is just a function from models of
spec2 to models of spec1. *)
Definition Interpretation spec1 spec2 :=
  spec_model spec2 -> spec_model spec1.

(* The identity interpretation *)
Program Definition interp_id (spec:Spec) : Interpretation spec spec := id.

(* Composing interpretations *)
Program Definition interp_compose {s1 s2 s3}
           (i2: Interpretation s2 s3) (i1: Interpretation s1 s2) :
  Interpretation s1 s3 := fun model3 => i1 (i2 model3).

(* Build an interpretation between the tails of two specs that have the same
head into an interpretation between the whole of the two specs *)
Definition interp_cons f T {spec1 spec2 : T -> Spec}
        (i: forall t, Interpretation (spec1 t) (spec2 t)) :
  Interpretation (Spec_Cons f T spec1)
                 (Spec_Cons f T spec2) :=
  fun model2:spec_model (Spec_Cons f T spec2) =>
    let (t,rest) := model2 in
    existT _ t (i _ rest).

(* Take an interpretation from spec1 to spec2 and cons an op onto spec2 *)
Definition interp_cons_r f T {spec1} {spec2: T -> Spec}
           (i: forall t, Interpretation spec1 (spec2 t)) :
  Interpretation spec1 (Spec_Cons f T spec2) :=
  fun model2:spec_model (Spec_Cons f T spec2) =>
    let (t,rest) := model2 in
    i t rest.


(*** Example Interpretations ***)

(* Interpret T as nat and n as n for spec_example_3 into spec_example_2 *)
Program Definition interp_example_3_2 :
  Interpretation spec_example_3 spec_example_2 :=
  (fun (model2:spec_model spec_example_2) =>
     match model2 with
       | existT _ n (existT _ n__proof ax_proof) =>
         (existT
            _ nat
            (existT
               _ _
               (existT _ n _))) : spec_model spec_example_3
     end).


(*** Pushouts ***)

(* A pushout of i1:spec->spec1 and i2:spec->spec2 is some spec' and two
interpretations i1':spec1->spec' and i2':spec2->spec' such that compose i1 i1'
equals compose i2 i2'. (Technically, a pushout is the "least" such spec, but it
is not really practical nor necessary to prove the leastness inside Coq) *)
Record Pushout {spec spec1 spec2} (i1: Interpretation spec spec1)
          (i2: Interpretation spec spec2) : Type :=
  {spec': Spec;
   i1': Interpretation spec1 spec';
   i2': Interpretation spec2 spec';
   pushout_pf: forall model', i1 (i1' model') = i2 (i2' model') }.


(*** Spec Extensions ***)

(* FIXME HERE: formalize SpecExtension (i.e., sub-specs) *)


(*** Spec Overlap ***)

(* NotInSpec f spec is a proof that f is not used as an op name in spec *)
Inductive NotInSpec (f:Field) : Spec -> Prop :=
| NotInSpec_base axioms : NotInSpec f (Spec_Axioms axioms)
| NotInSpec_cons f' T rest :
    f <> f' ->
    (forall t, NotInSpec f (rest t)) ->
    NotInSpec f (Spec_Cons f' T rest)
.

(* Tactic to prove NotInSpec goals *)
Ltac prove_not_in_spec :=
  match goal with
    | |- NotInSpec ?f (Spec_Cons ?f' _ _) =>
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
| SpecOverlap_eq f T rest1 rest2 :
    (forall t, SpecOverlap (rest1 t) (rest2 t)) ->
    SpecOverlap (Spec_Cons f T rest1) (Spec_Cons f T rest2)
| SpecOverlap_neq1 f1 T1 rest1 spec2 :
    NotInSpec f1 spec2 ->
    (forall t, SpecOverlap (rest1 t) spec2) ->
    SpecOverlap (Spec_Cons f1 T1 rest1) spec2
| SpecOverlap_neq2 f2 T2 rest2 spec1 :
    NotInSpec f2 spec1 ->
    (forall t, SpecOverlap spec1 (rest2 t)) ->
    SpecOverlap spec1 (Spec_Cons f2 T2 rest2)
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
    | |- SpecOverlap (Spec_Cons ?f1 ?T1 ?rest1)
                     (Spec_Cons ?f2 ?T2 ?rest2) =>
      lazymatch eval hnf in (Field_dec f1 f2) with
        | left _ =>
          (apply SpecOverlap_eq
                 || fail "Non-matching types or predicates at op" f1
                         ": types: " T1 ", " T2);
          intros; prove_spec_overlap
        | right ?neq =>
          ((apply SpecOverlap_neq1; [ prove_not_in_spec | intros ]) ||
           (apply SpecOverlap_neq2; [ prove_not_in_spec | intros ]) ||
           fail "The fields " f1 " and " f2 " appear to be in a different order in the two specs");
          prove_spec_overlap
      end
    | |- SpecOverlap (Spec_Cons _ _ _) (Spec_Axioms _) =>
      apply SpecOverlap_neq1; [ apply NotInSpec_base | intros; prove_spec_overlap ]
    | |- SpecOverlap (Spec_Axioms _) (Spec_Cons _ _ _) =>
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
        | |- SpecOverlap (Spec_Cons ?f1 ?T1 ?rest1)
                         (Spec_Cons ?f2 ?T2 ?rest2) =>
          idtac "prove_spec_overlapN: cons-cons";
          lazymatch eval hnf in (Field_dec f1 f2) with
            | left _ =>
              (apply SpecOverlap_eq
                     || fail "Non-matching types or predicates at op" f1
                             ": types: " T1 ", " T2);
              intros; prove_spec_overlapN n'
            | right ?neq =>
              ((apply SpecOverlap_neq1; [ prove_not_in_spec | intros ]) ||
               (apply SpecOverlap_neq2; [ prove_not_in_spec | intros ]) ||
               fail "The fields " f1 " and " f2 " appear to be in a different order in the two specs");
              prove_spec_overlapN n'
          end
        | |- SpecOverlap (Spec_Cons _ _ _) (Spec_Axioms _) =>
          idtac "prove_spec_overlapN: cons-axiom";
          apply SpecOverlap_neq1; [ apply NotInSpec_base | intros; prove_spec_overlapN n' ]
        | |- SpecOverlap (Spec_Axioms _) (Spec_Cons _ _ _) =>
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


(* FIXME HERE: define spec_of_overlap, which uses a SpecOverlap spec1 spec2 to
construct a spec that is an extension of both spec1 and spec2 *)


(*** Proving Isomorphisms between Type Classes and Specs ***)

(* FIXME HERE: figure out how to define this! *)

(*
Class IsoToSpecModels {spec} (ops: spec_ops spec) (P: Prop) : Prop :=
  spec_models_iso : P <-> spec_model spec ops.

(* Tactic to prove IsoToSpec instances *)
Ltac prove_spec_models_iso :=
  split; compute;
  [ intro H; destruct H;
    repeat (first [ assumption | split; [assumption|] | apply I])
  | intro H; repeat (let Hi := fresh "H" in
                     destruct H as [Hi H]); constructor; assumption ].
*)


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
Notation "'{*' elem1 , .. , elemn '*}'" :=
  (mkSpecTranslation (cons elem1%spec_translation_elem .. (cons elemn%spec_translation_elem nil) ..))
  (at level 0) : spec_translation_scope.
Notation "'{*' '*}'" :=
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
    | Spec_Cons f T rest =>
      Spec_Cons (translate_field xlate f) T
                  (fun x => translate_spec xlate (rest x))
  end.

(* NOTE: the spec_model type of a translated spec is in fact equal to that of
the original spec, but this requires functional extensionality to prove... *)

Lemma interp_translate_spec_axioms xlate axioms :
  Interpretation (Spec_Axioms axioms)
                 (Spec_Axioms (translate_spec_axioms xlate axioms)).
  induction axioms.
  intro; assumption.
  destruct axioms; destruct a.
  intro; assumption.
  intro H; destruct H; split.
  assumption.
  apply IHaxioms; assumption.
Defined.

Fixpoint interp_translate_spec xlate spec :
  Interpretation spec (translate_spec xlate spec) :=
  match spec return Interpretation spec (translate_spec xlate spec) with
    | Spec_Axioms axioms => interp_translate_spec_axioms xlate axioms
    | Spec_Cons f T rest =>
      fun model =>
        match model with
          | existT _ t model' =>
            existT _ t (interp_translate_spec xlate (rest t) model')
        end
  end.

Lemma interp_untranslate_spec_axioms xlate axioms :
  Interpretation (Spec_Axioms (translate_spec_axioms xlate axioms))
                 (Spec_Axioms axioms).
  induction axioms.
  intro; assumption.
  destruct axioms; destruct a.
  intro; assumption.
  intro H; destruct H; split.
  assumption.
  apply IHaxioms; assumption.
Defined.

(* Build an interpretation from (translate_spec xlate spec) back to spec *)
Fixpoint interp_untranslate_spec xlate spec :
  Interpretation (translate_spec xlate spec) spec :=
  match spec return Interpretation (translate_spec xlate spec) spec with
    | Spec_Axioms axioms => interp_untranslate_spec_axioms xlate axioms
    | Spec_Cons f T rest =>
      fun model =>
        match model with
          | existT _ t model' =>
            existT _ t (interp_untranslate_spec xlate (rest t) model')
        end
  end.

(* Translate an interpretation *)
Definition translate_interp {spec1 spec2} xlate
           (i: Interpretation spec1 spec2) :
  Interpretation (translate_spec xlate spec1) (translate_spec xlate spec2) :=
  interp_compose (interp_translate_spec xlate spec2)
                 (interp_compose i (interp_untranslate_spec xlate spec1)).


(***
 *** Building Interprations using Translations
 ***)

(* Like interp_cons, but allow the head op name to be translated and the type of
the head op to be strengthened *)
Definition interp_cons_strengthen_xlate xlate f1 T1 T2 {spec1 spec2}
           (impl: T2 -> T1)
           (i: forall t, Interpretation (spec1 (impl t)) (spec2 t)) :
  Interpretation (Spec_Cons f1 T1 spec1)
                 (Spec_Cons (translate_field xlate f1) T2 spec2) :=
  fun model2:spec_model (Spec_Cons (translate_field xlate f1) T2 spec2) =>
    let (t,model2') := model2 in
    existT _ (impl t) (i t model2').

(* Tactic to prove a "simple" interpretation, which is one where none of the ops
have to be re-ordered, but where the fields can be translated between the domain
spec and the co-domain spec. *)
(*
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
*)

(*
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
*)

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
(*
Ltac interp_tactic :=
  intros;
  lazymatch goal with
    | |- spec_model ?dom_spec (let (rest, t) := ?ops in ?body) =>
      destruct ops as [t ops]
    | |- Pred_Trivial _ => apply I
    | |- Pred_Fun _ => try assumption
    | |- _ => try (apply I); try assumption
  end.
*)


(*** Refinement ***)

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
(*
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
*)

(* Translate a refinement *)
Definition refinement_translate {spec}
           (R: RefinementOf spec) xlate : RefinementOf spec :=
  refinement_interp R (interp_translate_spec xlate _).
