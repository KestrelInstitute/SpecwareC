
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

(* Helper for building axiom pairs *)
Definition ax_pair (f:Field) (P:Prop) : (Field * Prop) :=
  pair f P.

Arguments ax_pair f%string P.

(* Unfold a definition *)
Definition def {T x} (t:T) (t__pf: t = x) : T := x.


(*** Models ***)

(* Helper for conjoining all the axioms in an axiom list *)
Fixpoint conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  match axioms with
    | [] => True
    | [p] => snd p
    | p :: axioms' => snd p /\ conjoin_axioms axioms'
  end.

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
Definition spec_example_1 :=
  Spec_ConsOp "n" nat Pred_Trivial
              (fun n _ => Spec_Axioms [ax_pair "gt1" (n > 1)]).

(* Example 2:  op n:nat := 2;  (no axioms) *)
Definition spec_example_2 :=
  Spec_ConsOp "n" nat (Pred_Eq 2)
              (fun n _ => Spec_Axioms []).

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Definition spec_example_3 :=
  Spec_ConsOp
    "T" Set (Pred_Eq nat)
    (fun T T__pf =>
       Spec_ConsOp "n" (def T T__pf) Pred_Trivial
                   (fun n _ => Spec_Axioms [ax_pair "gt1" (n > 1)])).

(* Example 4: Monoids *)
Definition spec_example_monoid :=
  Spec_ConsOp
    "T" Set Pred_Trivial
    (fun T _ =>
       Spec_ConsOp
         "m_zero" T Pred_Trivial
         (fun m_zero _ =>
            Spec_ConsOp
              "m_plus" (T -> T -> T) Pred_Trivial
              (fun m_plus _ =>
                 Spec_Axioms
                   [ax_pair "m_zero_left" (forall x, m_plus m_zero x = x);
                     ax_pair "m_zero_right" (forall x, m_plus x m_zero = x);
                     ax_pair "m_plus_assoc"
                             (forall x y z,
                                m_plus x (m_plus y z) = m_plus (m_plus x y) z)]))).

(* Example 5: Groups *)
Definition spec_example_group :=
  Spec_ConsOp
    "T" Set Pred_Trivial
    (fun T _ =>
       Spec_ConsOp
         "g_zero" T Pred_Trivial
         (fun g_zero _ =>
            Spec_ConsOp
              "g_plus" (T -> T -> T) Pred_Trivial
              (fun g_plus _ =>
                 Spec_ConsOp
                   "g_inv" (T -> T) Pred_Trivial
                   (fun g_inv _ =>
                        Spec_Axioms
                          [ax_pair "g_zero_left" (forall x, g_plus g_zero x = x);
                            ax_pair "g_zero_right" (forall x, g_plus x g_zero = x);
                            ax_pair "g_plus_assoc"
                                    (forall x y z,
                                       g_plus x (g_plus y z) = g_plus (g_plus x y) z);
                            ax_pair "g_inv_left"
                                    (forall (x:T), g_plus (g_inv x) x = g_zero);
                            ax_pair "g_inv_right"
                                    (forall (x:T), g_plus x (g_inv x) = g_zero)
    ])))).

(* Example 6: The Natural Numbers as a Monoid *)
Definition spec_example_natmonoid :=
Spec_ConsOp "T" Type (@Pred_Eq Type nat)
  (fun T__param T__proof =>
   Spec_ConsOp "m_zero" (def T__param T__proof) (Pred_Eq 0)
     (fun m_zero__param m_zero__proof =>
      Spec_ConsOp "m_plus"
        (def T__param T__proof ->
         def T__param T__proof -> def T__param T__proof) 
        (Pred_Eq Nat.add)
        (fun m_plus__param m_plus__proof
         =>
         Spec_Axioms
           (ax_pair "m_zero_left"
              (forall x : def T__param T__proof,
               def m_plus__param m_plus__proof
                 (def m_zero__param m_zero__proof) x = x)
            :: (ax_pair "m_zero_right"
                  (forall x : def T__param T__proof,
                   def m_plus__param m_plus__proof x
                     (def m_zero__param m_zero__proof) = x)
                :: ax_pair "m_plus_assoc"
                     (forall x y z : def T__param T__proof,
                      def m_plus__param m_plus__proof x
                        (def m_plus__param m_plus__proof y z) =
                      def m_plus__param m_plus__proof
                        (def m_plus__param m_plus__proof x y) z) :: nil)%list)))).

Definition spec_example_ops_natmonoid
           T__param T__proof m_zero__param m_zero__proof m_plus__param m_plus__proof :
  spec_ops spec_example_natmonoid :=
  (@existT) _ _ T__param
    ((@existT) _ _ T__proof
       ((@existT) _ _ m_zero__param
          ((@existT) _ _ m_zero__proof
             ((@existT) _ _ m_plus__param
                ((@existT) _ _ m_plus__proof ((@tt))))))).

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
  spec_model spec_example_natmonoid
             (spec_example_ops_natmonoid T__param T__proof m_zero__param
                                         m_zero__proof m_plus__param m_plus__proof) :=
  conj m_zero_left__param (conj m_zero_right__param m_plus_assoc__param).


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
  mkInterp (fun ops2:spec_ops (Spec_ConsOp f T oppred spec2) =>
              let (t_o,o) := ops2 in
              let (pf_o, rest_o) := o in
              ops_cons t_o pf_o (map_ops (i _ _) rest_o))
           (fun ops2 =>
              match ops2
                    return spec_model (Spec_ConsOp f T oppred spec2) ops2 ->
                           spec_model
                             (Spec_ConsOp f T oppred spec1)
                             (let (t_o,o) := ops2 in
                              let (pf_o,rest_o) := o in
                              ops_cons t_o pf_o (map_ops (i _ _) rest_o)) with
                | existT _ t_o (existT _ pf_o rest_o) =>
                  fun model2 =>
                    map_model (i t_o pf_o) rest_o model2
              end).

(* The simpler version, that does not destruct ops2. We choose the above version
to make it more efficient to compute with this interpretation. *)
(*
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
*)

(* Take an interpretation from spec1 to spec2 and cons an op onto spec2 *)
Definition interp_cons_r f T (oppred: OpPred T)
           {spec1} {spec2: forall t, oppred t -> Spec}
           (i: forall t pfs, Interpretation spec1 (spec2 t pfs)) :
  Interpretation spec1 (Spec_ConsOp f T oppred spec2) :=
  mkInterp (fun ops2:spec_ops (Spec_ConsOp f T oppred spec2) =>
              let (t_o,o) := ops2 in
              let (pf_o,rest_o) := o in
              map_ops (i t_o pf_o) rest_o)
           (fun ops2 =>
              match ops2
                    return spec_model (Spec_ConsOp f T oppred spec2) ops2 ->
                           spec_model spec1
                                      (let (t_o,o) := ops2 in
                                       let (pf_o,rest_o) := o in
                                       map_ops (i _ _) rest_o) with
                | existT _ t_o (existT _ pf_o rest_o) =>
                  fun model2 =>
                    map_model (i t_o pf_o) rest_o model2
              end).


(* The simpler version, that does not destruct ops2. We choose the above version
to make it more efficient to compute with this interpretation. *)
(*
Definition interp_cons_r f T (oppred: OpPred T)
           {spec1} {spec2: forall t, oppred t -> Spec}
           (i: forall t pfs, Interpretation spec1 (spec2 t pfs)) :
  Interpretation spec1 (Spec_ConsOp f T oppred spec2) :=
  mkInterp (fun ops2 => map_ops (i (ops_head ops2) (ops_proof ops2)) (ops_rest ops2))
           (fun ops2 model2 => map_model (i (ops_head ops2) (ops_proof ops2)) _ model2).
*)


(*** Example Interpretations ***)

(* Interpret T as nat and n as n for spec_example_3 into spec_example_2 *)
Program Definition interp_example_3_2 : Interpretation spec_example_3 spec_example_2 :=
  fun ops2 =>
    (ops_cons (oppred:= Pred_Eq nat) nat eq_refl
              (ops_cons (oppred:=Pred_Trivial) (ops_head ops2) I (tt : spec_ops (Spec_Axioms _)))) : spec_ops spec_example_3.

(* Interpret monoids in groups *)
(* FIXME: this sucks! *)
(*
Program Definition interp_example_monoid_group :
  Interpretation spec_example_monoid spec_example_group :=
  fun ops_g =>
    (ops_cons
       (oppred:=None) (ops_head ops_g) (ops_proof ops_g)
       (ops_cons
          (oppred:=None) ))
*)


(*** Appending Specs ***)

(* Append axioms to the end of a spec *)
Fixpoint spec_append_axioms spec axioms2 : Spec :=
  match spec with
    | Spec_Axioms axioms1 => Spec_Axioms (axioms1 ++ axioms2)
    | Spec_ConsOp f T oppred rest =>
      Spec_ConsOp f T oppred (fun t pf => spec_append_axioms (rest t pf) axioms2)
  end.

Lemma conjoin_axioms_append1 axioms1 axioms2 :
  conjoin_axioms (axioms1 ++ axioms2) -> conjoin_axioms axioms1.
  induction axioms1.
  intros; constructor.
  destruct axioms1.
  destruct axioms2.
  intros; assumption.
  intro H; destruct H; assumption.
  intro H; destruct H; split.
  assumption.
  apply IHaxioms1; assumption.
Qed.

Lemma conjoin_axioms_append2 axioms1 axioms2 :
  conjoin_axioms (axioms1 ++ axioms2) -> conjoin_axioms axioms2.
  induction axioms1; intros.
  assumption.
  apply IHaxioms1.
  destruct axioms1.
  destruct axioms2; [ constructor | destruct H; assumption ].
  destruct H; assumption.
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


(*** Sub-Specs ***)

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

(* There is always an interpretation from a sub-spec to a super-spec *)
Fixpoint sub_spec_interp {spec1 spec2} (sub: SubSpec spec1 spec2) :
  Interpretation spec1 spec2 :=
  match sub in SubSpec spec1 spec2 return Interpretation spec1 spec2 with
    | SubSpec_base axioms spec2 model_f =>
      mkInterp (fun _ => tt : spec_ops (Spec_Axioms axioms)) model_f
    | SubSpec_eq f T oppred rest1 rest2 sub' =>
      interp_cons f T oppred (fun t pf => sub_spec_interp (sub' t pf))
    | SubSpec_neq spec1 f2 T2 oppred2 rest2 sub' =>
      interp_cons_r f2 T2 oppred2 (fun t pf => sub_spec_interp (sub' t pf))
  end.

(* Helper for automatically building SubSpec proofs *)
Lemma sub_spec_axioms_eq f P axs1 axs2 :
  (conjoin_axioms axs1 -> conjoin_axioms axs2) ->
  conjoin_axioms (ax_pair f P::axs1) -> conjoin_axioms (ax_pair f P::axs2).
  destruct axs1; destruct axs2; intros impl pf1.
  assumption.
  split; [ assumption | apply impl; apply I ].
  destruct pf1; assumption.
  destruct pf1; split; [ assumption | apply impl; assumption ].
Qed.

(* Helper for automatically building SubSpec proofs *)
Lemma sub_spec_axioms_neq f P axs1 axs2 :
  (conjoin_axioms axs1 -> conjoin_axioms axs2) ->
  conjoin_axioms (ax_pair f P::axs1) -> conjoin_axioms axs2.
  destruct axs1; intros impl pf1; apply impl.
  apply I.
  destruct pf1; assumption.
Qed.

(* Tactic to prove SubSpec goals generated by imports *)
Ltac prove_sub_spec :=
  repeat (first [apply SubSpec_eq; intros |
                 apply SubSpec_neq; intros]);
  apply SubSpec_base; intro;
  repeat (first [ apply sub_spec_axioms_eq | apply sub_spec_axioms_neq ]);
  intro; assumption.


(*** Spec Substitution ***)

(* Subtract sub-spec spec1 from super-spec spec2, given ops for spec1 *)
Fixpoint spec_subtract spec1 spec2 (sub: SubSpec spec1 spec2) :
  spec_ops spec1 -> Spec :=
  match sub in SubSpec spec1 spec2 return spec_ops spec1 -> Spec with
    | SubSpec_base axioms spec2 axioms_pf => fun _ => spec2
    | SubSpec_eq f T oppred rest1 rest2 sub' =>
      fun ops1 =>
        match ops1 with
          | existT _ t_o (existT _ pf_o rest_o) =>
            spec_subtract _ _ (sub' t_o pf_o) rest_o
        end
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
        match ops1 with
          | existT _ t_o (existT _ pf_o rest_o) =>
            mkInterp (fun ops_sub =>
                        ops_cons t_o pf_o
                                 (map_ops (spec_subtract_interp
                                             _ _ (sub' _ _) rest_o)
                                          ops_sub))
                     (map_model (spec_subtract_interp _ _ _ rest_o))
        end
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

(* Replace all the trivial True proofs in a spec_ops with I *)
Fixpoint replace_op_proofs spec : spec_ops spec -> spec_ops spec :=
  match spec with
    | Spec_Axioms _ => fun ops => ops
    | Spec_ConsOp f T oppred rest =>
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
    | Spec_ConsOp f T oppred rest =>
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

(* Whether P is isomorphic to spec *)
Class IsoToSpec spec (P: OpsPred spec) : Prop :=
  spec_iso: forall ops, ApplyOps spec _ P ops <-> spec_model spec ops.

(* FIXME HERE: figure out how to define IsoInterpretations *)

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
FIXME HERE: the below loops forever!

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
| XlateWild (f_from_prefix f_to_prefix : string)
.

Arguments XlateSingle (f_from%string) (f_to%string).
Arguments XlateWild (f_from_prefix%string) (f_to_prefix%string).

(* A spec translation is just a list of spec translation elements *)
Inductive SpecTranslation : Set :=
| mkSpecTranslation (elems: list SpecTranslationElem).

Notation "f_from '+->' f_to" :=
  (XlateSingle f_from f_to)
  (at level 80, no associativity) : spec_translation_elem_scope.
Notation "f_from '%' '+->' f_to '%'" :=
  (XlateWild f_from f_to)
  (at level 80, no associativity) : spec_translation_elem_scope.

Bind Scope spec_translation_elem_scope with SpecTranslationElem.
Delimit Scope spec_translation_elem_scope with spec_translation_elem.

(* We use double curly brackets to write spec translations *)
Notation "'{{' elem1 , .. , elemn '}}'" :=
  (mkSpecTranslation (cons elem1%spec_translation_elem .. (cons elemn%spec_translation_elem nil) ..))
  (at level 0).
Notation "'{{' '}}'" :=
  (mkSpecTranslation nil)
  (at level 0).

Definition translate_field1 elem (f: Field) : option Field :=
  match elem with
    | XlateSingle f_from f_to =>
      if Field_dec f f_from then Some f_to else None
    | XlateWild f_from_prefix f_to_prefix =>
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

Definition translate_spec_axioms xlate axioms : list (Field * Prop) :=
  map (fun fP =>
         match fP with
           | (f, P) => (translate_field xlate f, P)
         end) axioms.

Fixpoint translate_spec xlate spec : Spec :=
  match spec with
    | Spec_Axioms axioms =>
      Spec_Axioms (translate_spec_axioms xlate axioms)
    | Spec_ConsOp f T oppred rest =>
      Spec_ConsOp (translate_field xlate f) T oppred
                  (fun x x__pf => translate_spec xlate (rest x x__pf))
  end.

(* NOTE: the spec_ops type of a translated spec is in fact equal to that of the
original spec, but this requires functional extensionality to prove... *)

Fixpoint translate_spec_ops xlate spec :
  spec_ops (translate_spec xlate spec) -> spec_ops spec :=
  match spec return spec_ops (translate_spec xlate spec) -> spec_ops spec with
    | Spec_Axioms _ => fun ops => ops
    | Spec_ConsOp f T oppred rest =>
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
    | Spec_ConsOp f T oppred rest =>
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
  Interpretation (Spec_ConsOp f1 T oppred1 spec1)
                 (Spec_ConsOp (translate_field xlate f1) T oppred2 spec2) :=
  mkInterp (fun ops2:spec_ops (Spec_ConsOp (translate_field xlate f1)
                                           T oppred2 spec2) =>
              let (t_o,o) := ops2 in
              let (pf_o, rest_o) := o in
              ops_cons t_o (impl _ pf_o) (map_ops (i t_o pf_o) rest_o))
           (fun ops2 =>
              match ops2
                    return spec_model (Spec_ConsOp (translate_field xlate f1)
                                                   T oppred2 spec2) ops2 ->
                           spec_model
                             (Spec_ConsOp f1 T oppred1 spec1)
                             (let (t_o,o) := ops2 in
                              let (pf_o,rest_o) := o in
                              ops_cons t_o (impl t_o pf_o) (map_ops (i _ _) rest_o)) with
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
  Interpretation (Spec_ConsOp f1 T1 oppred1 spec1)
                 (Spec_ConsOp (translate_field xlate f1) T2 oppred2 spec2) :=
  mkInterp (fun ops2:spec_ops (Spec_ConsOp (translate_field xlate f1)
                                           T2 oppred2 spec2) =>
              let (t_o,o) := ops2 in
              let (pf_o, rest_o) := o in
              ops_cons (rew eT in t_o) (impl _ pf_o) (map_ops (i t_o pf_o) rest_o))
           (fun ops2 =>
              match ops2
                    return spec_model (Spec_ConsOp (translate_field xlate f1)
                                                   T2 oppred2 spec2) ops2 ->
                           spec_model
                             (Spec_ConsOp f1 T1 oppred1 spec1)
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
Ltac prove_simple_interp xlate :=
  let next :=
      lazymatch goal with
      | |- Interpretation (Spec_ConsOp ?f1 ?T1 ?oppred1 ?rest1)
                          (Spec_ConsOp ?f2 ?T2 ?oppred2 ?rest2) =>
        lazymatch (eval cbn in (Field_dec f2 (translate_field xlate f1))) with
          | left _ =>
            idtac "equal fields";
              first
                [ apply (interp_cons_strengthen_xlate xlate); intros;
                  [ try_prove_simple_interp_pred | prove_simple_interp xlate ]
                | (let eT := fresh "eT" in
                   let eT := evar (eT:@eq Type T2 T1) in
                   apply (interp_cons_strengthen_xlate_eq
                            xlate f1 T1 T2 oppred1 oppred2 eT);
                   intros; [ try_prove_simple_interp_pred
                           | prove_simple_interp xlate ]) ]
          | right _ =>
            idtac "unequal fields"; apply interp_cons_r; intros;
            prove_simple_interp xlate
        end
      | |- Interpretation (Spec_Axioms _)
                          (Spec_ConsOp ?f1 ?T1 ?oppred1 ?rest1) =>
        idtac "axioms on the left";
        apply interp_cons_r; intros;
        prove_simple_interp xlate
      | |- Interpretation (Spec_Axioms _) (Spec_Axioms _) =>
        idtac "axioms";
        apply (mkInterp (fun _ => tt : spec_ops (Spec_Axioms _))); intros ops model;
        unfold spec_model, conjoin_axioms, ax_pair, snd in model;
        repeat (let ax_name := fresh "axiom" in
                first [ destruct model as [ax_name model] | rename model into ax_name ]);
        unfold spec_model, conjoin_axioms, ax_pair, snd; repeat split;
        try assumption
      | |- Interpretation ?S1 ?S2 =>
        let S1' := (eval hnf in S1) in
        let S2' := (eval hnf in S2) in
        (progress (change S1 with S1'; change S2 with S2');
         idtac "evaluating interp spec terms";
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
  unfold spec_model, conjoin_axioms, ax_pair, snd in model;
  repeat (let ax_name := fresh "axiom" in
          first [ destruct model as [ax_name model] | rename model into ax_name ]);
  unfold spec_model, conjoin_axioms, ax_pair, snd; repeat split;
  try assumption.
*)


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
           (R: RefinementOf spec) (sub: SubSpec spec1 (ref_spec _ R))
           (i: Interpretation spec1 spec2) : RefinementOf spec :=
  refinement_interp R (spec_subst_interp1 sub i).

(* Apply a spec substitution to a refinement, importing the co-domain spec *)
Definition refinement_subst {spec spec1 spec2}
           (R: RefinementOf spec) (i: Interpretation spec1 spec2) :
  SubSpec spec1 (ref_spec _ R) -> RefinementOf spec :=
  match R as R return SubSpec spec1 (ref_spec _ R) -> RefinementOf spec with
    | Build_RefinementOf _ spec' interp imps =>
      fun (sub: SubSpec spec1 spec') =>
        {| ref_spec := spec_subst sub i;
           ref_interp := interp_compose (spec_subst_interp1 sub i) interp;
           ref_imports :=
             {| ref_import_fromspec := spec2;
                ref_import_interp := spec_subst_interp2 sub i |}
               ::(map (fun imp => refinement_import_interp
                                    imp (spec_subst_interp1 sub i)) imps) |}
  end.

(* FIXME: document this *)
Definition spec_subst_interp2_xlate {spec1sub spec1 spec2}
           xlate (sub: SubSpec (translate_spec xlate spec1sub) spec1)
           (i: Interpretation spec1sub spec2) :
  Interpretation spec2 (spec_subst sub (translate_interp xlate i)) :=
 interp_compose (interp_append1 _ _) (interp_translate_spec _ _).

(* Apply a spec substitution to a refinement, using the translation of an
interpretation, importing the un-translated co-domain of the interpretation *)
Definition refinement_subst_xlate {spec spec1 spec2}
           (R: RefinementOf spec) (i: Interpretation spec1 spec2) xlate :
  SubSpec (translate_spec xlate spec1) (ref_spec _ R) -> RefinementOf spec :=
  match R as R return SubSpec (translate_spec xlate spec1) (ref_spec _ R) ->
                      RefinementOf spec with
    | Build_RefinementOf _ spec' interp imps =>
      fun (sub: SubSpec (translate_spec xlate spec1) spec') =>
        {| ref_spec := spec_subst sub (translate_interp xlate i);
           ref_interp :=
             interp_compose (spec_subst_interp1
                               sub (translate_interp xlate i)) interp;
           ref_imports :=
             {| ref_import_fromspec := spec2;
                ref_import_interp := spec_subst_interp2_xlate xlate sub i |}
               ::(map (fun imp => refinement_import_interp
                                    imp (spec_subst_interp1
                                           sub (translate_interp xlate i))) imps) |}
  end.

(* Translate a refinement *)
Definition refinement_translate {spec}
           (R: RefinementOf spec) xlate : RefinementOf spec :=
  refinement_interp R (interp_translate_spec xlate _).
