
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


(*** Field lists with no duplicates ***)

Inductive flist : list Field -> Set :=
| fnil : flist []
| fcons f {l} (not_in : ~In f l) (flist' : flist l) : flist (f::l)
.

Lemma flist_NoDup {l} (fl : flist l) : NoDup l.
  induction fl; constructor; assumption.
Qed.

Fixpoint fremove1 f l :=
  match l with
    | [] => []
    | f'::l' =>
      if Field_dec f f' then l' else
        f' :: fremove1 f l'
  end.

Lemma fremove1_eq f f' l : f = f' -> fremove1 f (f'::l) = l.
  intro e; rewrite <- e. unfold fremove1; fold (fremove1 f).
  destruct (Field_dec_eq f) as [e2 e3]; rewrite e3.
  reflexivity.
Qed.

Lemma fremove1_neq f f' l : f <> f' -> fremove1 f (f'::l) = f':: fremove1 f l.
  intro neq. unfold fremove1; fold (fremove1 f).
  destruct (Field_dec_neq f f' neq) as [e2 e3]; rewrite e3.
  reflexivity.
Qed.

Lemma not_in_fremove1 f f' l : ~In f' l -> ~In f' (fremove1 f l).
  induction l; intro not_in.
  intro H; apply H.
  unfold fremove1; fold (fremove1 f).
  assert (~In f' l) as H.
  intro i; apply not_in; apply in_cons; assumption.
  destruct (Field_dec f a).
  assumption.
  intro H0; destruct H0.
  apply not_in; rewrite H0; left; reflexivity.
  apply IHl; assumption.
Qed.

Fixpoint fl_remove f {l} (fl : flist l) : flist (fremove1 f l) :=
  match fl in flist l return flist (fremove1 f l) with
    | fnil => fnil
    | fcons f' not_in fl' =>
      match Field_dec f f' with
        | left e =>
          rew [flist] (eq_sym (fremove1_eq _ _ _ e)) in fl'
        | right neq =>
          rew [flist] (eq_sym (fremove1_neq _ _ _ neq)) in
              (fcons f' (not_in_fremove1 _ _ _ not_in) (fl_remove f fl'))
      end
  end.

Definition in_fl f {l} (fl : flist l) : Prop := In f l.

Definition in_fl_dec f {l} fl : {@in_fl f l fl} + {~ @in_fl f l fl} :=
  In_dec Field_dec f l.

Lemma in_fl_eq f {l} not_in fl : @in_fl f (f::l) (fcons f not_in fl).
  left; reflexivity.
Qed.

Lemma in_fl_cons {f l not_in fl} f' : in_fl f' fl -> in_fl f' (@fcons f l not_in fl).
  intro i. right. assumption.
Qed.

Lemma in_fl_tail {f' l fl not_in} f :
  f <> f' -> in_fl f (@fcons f' l not_in fl) -> in_fl f fl.
  intros neq i; destruct i.
  elimtype False; apply neq; symmetry; assumption.
  assumption.
Qed.

(* In proofs in lists without duplicates are always equal *)
Lemma in_fl_uniq (f:Field) l (nd:NoDup l) (in1 in2 : In f l) : in1 = in2.
  induction l.
  elimtype False; assumption.
  unfold In in in1,in2; fold (In f l) in in1,in2.
  destruct in1; destruct in2.
  rewrite (UIP_dec Field_dec e e0); reflexivity.
  elimtype False; apply (NoDup_remove_2 [] l a nd); rewrite e; assumption.
  elimtype False; apply (NoDup_remove_2 [] l a nd); rewrite e; assumption.
  f_equal; apply (IHl (NoDup_remove_1 [] l a nd)).
Qed.

(* Helper lemma for proving a field is not in a list *)
Definition not_in_cons A (f f':A) l : f<>f' -> ~In f l -> ~In f (f'::l).
  intros neq not_in i; destruct i.
  apply neq; symmetry; assumption.
  contradiction.
Qed.

(* Tactic for proving a field is not in a list *)
Ltac solve_not_in_list :=
  match goal with
    | |- (~In ?f (@nil _)) => intro; assumption
    | |- (~In ?f ?l) => apply not_in_cons; [ intro; discriminate | ]; try solve_not_in_list
    | |- ?goal => fail "solve_not_in_list" goal
  end.


(*** Specs ***)

(* The inductive representation of specs, indexed by the op fields *)
Inductive SpecRepr : forall {l}, flist l -> Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : SpecRepr fnil
(* The inductive case adds an op named f with zero or more definitions to the
rest of the spec, that can depend on any f equal to all the definitions *)
| Spec_ConsOp f {l flds} not_in (T : Type) (constraint: T -> Prop)
              (rest : forall t, constraint t -> SpecRepr flds)
  : SpecRepr (@fcons f l not_in flds)
.

(* Make the field argument be parsed by Coq as a string *)
Arguments Spec_ConsOp f%string l flds not_in T constraint rest.

(* A bundled type for specs and their fields *)
Definition Spec : Type := {l:_ & {fl:_ & @SpecRepr l fl}}.

(* Build a Spec, leaving l and fl implicit *)
Definition mkSpec {l fl} srepr : Spec := existT _ l (existT _ fl srepr).

(* Extract the flist out of a Spec *)
Definition specFields (spec:Spec) := (projT1 (projT2 spec)).

(* Extract the representation out of a Spec *)
Definition specRepr (spec:Spec) := projT2 (projT2 spec).


(*** Models of a Spec ***)

(* Helper for elements of a model at an arbitrary type *)
Definition Any : Type := { T : Type & T }.
Definition mkAny (T:Type) (t:T) : Any := existT (fun T => T) T t.

(* Helper for conjoining all the axioms in an axiom list *)
Fixpoint conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_left (fun P1 f_P2 => and P1 (snd f_P2)) axioms True.

(* Build the type of the models of spec as a nested dependent pair *)
Fixpoint spec_repr_model {l flds} (spec:@SpecRepr l flds) : Type :=
  match spec with
    | Spec_Axioms axioms =>
      conjoin_axioms axioms
    | Spec_ConsOp f not_in T constraint rest =>
      { t : T & {pf: constraint t & spec_repr_model (rest t pf)}}
  end.

Definition spec_model (spec:Spec) := spec_repr_model (specRepr spec).


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
  Spec_ConsOp "n" _ nat (fun _ => True)
              (fun n _ => Spec_Axioms [("gt1"%string, n > 1)]).

(* Example 2:  op n:nat := 2;  (no axioms) *)
Program Definition spec_repr_example_2 :=
  Spec_ConsOp "n" _ nat (fun n => n = 2)
              (fun n _ => Spec_Axioms []).

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Program Definition spec_repr_example_3 :=
  Spec_ConsOp
    "T" _ Set (fun T => T = nat)
    (fun T T__pf =>
       Spec_ConsOp "n" _ T (fun _ => True)
                   (fun n _ => Spec_Axioms [("gt1"%string, (rew T__pf in n) > 1)])).
Next Obligation.
intro. destruct H. discriminate. assumption.
Defined.
Next Obligation.
exact x.
Defined.
Print spec_repr_example_3.


(*** Interpretations ***)

(* An interpretation of source in target is a mapping from models of target to
models of source *)
Definition Interpretation source target : Type :=
  spec_model target -> spec_model source.

(* The identity interpretation *)
Definition interp_id (spec:Spec) : Interpretation spec spec := id.

(* Composing interpretations *)
Definition interp_compose {s1 s2 s3}
           (i2: Interpretation s2 s3) (i1: Interpretation s1 s2) :
  Interpretation s1 s3 :=
  fun model => i1 (i2 model).


(*** Interpretations on the tail of a spec ***)

(* A dependent spec is a spec inside a binder; note that the field list is not
inside the scope of the binder *)
Definition DepSpec T constraint : Type :=
  {l:_ & {fl:_ & forall t:T, constraint t -> @SpecRepr l fl}}.

(* Project out the SpecRepr of a DepSpec *)
Definition depSpecRepr {T constraint} (spec: DepSpec T constraint) :=
  projT2 (projT2 spec).

(* Add an op to the beginning of a DepSpec to get a Spec *)
Definition depSpec_ConsOp f T constraint (spec: DepSpec T constraint) not_in : Spec :=
  existT _ _ (existT _ _ (Spec_ConsOp f not_in T constraint (depSpecRepr spec))).

(* A dependent interpretation is interpretation inside a binder; note that the
mapping is not inside the scope of the binder *)
Definition DepInterpretation {T constraint} (source target: DepSpec T constraint) :=
  forall t pf, spec_repr_model (depSpecRepr target t pf) ->
               spec_repr_model (depSpecRepr source t pf).

(* Cons an op onto the front of a dependent interpretation *)
Definition interp_cons f {T} constraint {s1 s2} not_in1 not_in2
           (interp : @DepInterpretation T constraint s1 s2) :
  Interpretation (depSpec_ConsOp f T constraint s1 not_in1)
                 (depSpec_ConsOp f T constraint s2 not_in2) :=
  fun model =>
    existT _ (projT1 model)
           (existT _ (projT1 (projT2 model))
                   (interp _ _ (projT2 (projT2 model)))).


(*** Sub-Specs and Spec Substitution ***)

Inductive SubSpecRepr : forall {l1 fl1 l2 fl2},
                          @SpecRepr l1 fl1 -> @SpecRepr l2 fl2 -> Type :=
| SubSpec_base {l2 fl2} srepr2 axioms :
    (spec_repr_model srepr2 -> conjoin_axioms axioms) ->
    @SubSpecRepr _ _ l2 fl2 (Spec_Axioms axioms) srepr2
| SubSpec_eq {l1 fl1 l2 fl2} f not_in1 not_in2 T
             (constraint1 constraint2 : T -> Prop) rest1 rest2
             (pf1_f: forall t, constraint2 t -> constraint1 t) :
    (forall t pf2,
       @SubSpecRepr l1 fl1 l2 fl2 (rest1 t (pf1_f t pf2)) (rest2 t pf2)) ->
    SubSpecRepr (Spec_ConsOp f not_in1 T constraint1 rest1)
                (Spec_ConsOp f not_in2 T constraint2 rest2)
| SubSpec_neq {l1 fl1 l2 fl2} srepr1 f not_in2 T
             (constraint2 : T -> Prop) rest2 :
    (forall t pf, @SubSpecRepr l1 fl1 l2 fl2 srepr1 (rest2 t pf)) ->
    SubSpecRepr srepr1 (Spec_ConsOp f not_in2 T constraint2 rest2)
.


(* FIXME HERE: old stuff below... *)

(* This holds iff field f has type T and a constraint at least as strong as
constraint in srepr. We put it in Type so we can recurse on it. *)
(*
Inductive field_in_spec_repr f T constraint : forall {l fl}, @SpecRepr l fl -> Type :=
| field_in_base {l fl} not_in (constraint' : T -> Prop) rest :
    (forall t, constraint' t -> constraint t) ->
    field_in_spec_repr f T constraint (@Spec_ConsOp f l fl not_in T constraint' rest)
| field_in_cons f' {l fl} not_in T' constraint' rest :
    (forall t pf, field_in_spec_repr f T constraint (rest t pf)) ->
    field_in_spec_repr f T constraint (@Spec_ConsOp f' l fl not_in T' constraint' rest)
.
*)

(* This holds iff field f has type T and a constraint that satisfies t. We put
it in Type so we can recurse on it. *)
(*
Inductive field_satisfies_spec f T t : Spec -> Type :=
| field_sats_base {l fl} not_in (constraint : T -> Prop) rest :
    constraint t ->
    field_satisfies_spec f T t (mkSpec (@Spec_ConsOp f l fl not_in T constraint rest))
| field_sats_cons f' {l fl} not_in T' constraint rest :
    (forall t' pf, field_satisfies_spec f T t (mkSpec (rest t' pf))) ->
    field_satisfies_spec f T t (mkSpec (@Spec_ConsOp f' l fl not_in T' constraint rest))
.
*)

(* Substitute a value for a field in a spec repr *)
(*
Fixpoint subst_spec_field f T t spec (sats: field_satisfies_spec f T t spec) : Spec :=
  match sats with
    | field_sats_base not_in constraint rest pf =>
      rest t pf
    | field_sats_cons f' not_in T' constraint rest sats' =>
      mkSpec (Spec_ConsOp f' not_in T' constraint
                          (fun t' pf' => specRepr subst_spec_field f T t ))

    | Spec_Axioms [] =>
      fun sats => match sats with end
    | Spec_ConsOp f' not_in T' constraint rest =>
      fun sats =>
        match Field_dec f f' with
          | left e =>
            match (proj1 (sats e)) with
              | ex_intro _ eT constr_pf =>
                rew [fun p => @SpecRepr (projT1 p) (projT2 p)] _ in
                    (rest (rew eT in t) constr_pf)
            end
          | right neq =>
            rew [fun p => @SpecRepr (projT1 p) (projT2 p)] _ in
*)

(*
Fixpoint field_satisfies_spec f T t {l fl} (srepr: @SpecRepr l fl) : Prop :=
  match srepr with
    | Spec_Axioms _ => False
    | Spec_ConsOp f' not_in T' constraint rest =>
      (f = f' -> exists (e : T = T'), constraint (rew e in t)) /\
      (f <> f' ->
       forall t' pf, field_satisfies_spec f T t (rest t' pf))
  end.

Program Fixpoint rem_spec_field f T t {l fl} srepr
        (i: field_in_spec_repr )
 :
  @field_satisfies_spec f T t l fl srepr -> SpecRepr (fl_remove f fl) :=
  match srepr with
    | Spec_Axioms [] =>
      fun sats => match sats with end
    | Spec_ConsOp f' not_in T' constraint rest =>
      fun sats =>
        match Field_dec f f' with
          | left e =>
            match (proj1 (sats e)) with
              | ex_intro _ eT constr_pf =>
                rew [fun p => @SpecRepr (projT1 p) (projT2 p)] _ in
                    (rest (rew eT in t) constr_pf)
            end
          | right neq =>
            rew [fun p => @SpecRepr (projT1 p) (projT2 p)] _ in
*)
                
