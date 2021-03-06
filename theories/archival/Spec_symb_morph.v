
(*** Modeling specs and morphisms as Coq terms ***)

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


(*** Maps on fields ***)

Definition FMap := Field -> Field.

Definition fmap_id : FMap := id.

Definition fmap_compose (m2 m1 : FMap) : FMap :=
  fun f => m2 (m1 f).

Definition fmap_cons f (m:FMap) : FMap :=
  fun f' => if Field_dec f f' then f else m f'.


(*** Models ***)

(* Helper for elements of a model at an arbitrary type *)
Definition Any : Type := { T : Type & T }.
Definition mkAny (T:Type) (t:T) : Any := existT (fun T => T) T t.
Definition anyType (any:Any) : Type := projT1 any.
Definition anyObj (any:Any) : anyType any := projT2 any.

(* A model is maps fields to ops for those fields *)
Definition Model : Type := Field -> Any.

(* Model equivalence is extensional equality (without needing an axiom) *)
Definition model_equiv (model1 model2 : Model) : Prop :=
  forall f, model1 f = model2 f.

(* Model equivalence on a restricted domain *)
Definition model_equiv_on {l} fl (model1 model2 : Model) : Prop :=
  forall f, @in_fl f l fl -> model1 f = model2 f.

(* Model equivalence on fl -> equivalence on the tail of fl *)
Lemma model_equiv_on_tail {f l not_in fl} (model1 model2 : Model) :
  model_equiv_on (@fcons f l not_in fl) model1 model2 ->
  model_equiv_on fl model1 model2.
  intros equiv f' i; apply equiv; apply in_fl_cons; assumption.
Qed.

(* General model equivalence -> equivalence on any fl *)
Lemma model_equiv_on_any {l} fl (model1 model2 : Model) :
  model_equiv model1 model2 ->
  @model_equiv_on l fl model1 model2.
  intros equiv f i; apply equiv.
Qed.

(* Whether f has type T in model *)
Definition has_type_in_model f T (model: Model) : Prop :=
  anyType (model f) = T.

(* has_type_in_model is equal in models that are equivalent on it *)
Lemma has_type_in_model_equiv_f f T model1 model2 :
  model1 f = model2 f ->
  has_type_in_model f T model1 = has_type_in_model f T model2.
  intros e; unfold has_type_in_model; rewrite <- e; reflexivity.
Qed.

(* has_type_in_model is equal in equivalent models *)
Lemma has_type_in_model_equiv f T model1 model2 :
  model_equiv model1 model2 ->
  has_type_in_model f T model1 = has_type_in_model f T model2.
  intros equiv; unfold has_type_in_model; rewrite <- equiv; reflexivity.
Qed.

(* Project field f from model *)
Definition model_proj f T (model: Model)
         (htim: has_type_in_model f T model) : T :=
  rew [id] htim in (anyObj (model f)).

(* model_proj is equal (modulo htim proof) in equivalent models *)
Lemma model_proj_equiv f T model1 model2 htim :
  model_equiv model1 model2 ->
  exists htim', model_proj f T model1 htim = model_proj f T model2 htim'.
  unfold model_proj; unfold has_type_in_model.
  intros equiv; rewrite <- (equiv f). exists htim. reflexivity.
Qed.

(* model_proj is equal (modulo htim proof) in equivalent models *)
Lemma model_proj_equiv_f f T model1 model2 htim :
  model1 f = model2 f ->
  exists htim', model_proj f T model1 htim = model_proj f T model2 htim'.
  unfold model_proj; unfold has_type_in_model.
  intros e; rewrite <- e. exists htim. reflexivity.
Qed.

(* Build a model with a subset of the fields in flds by mapping each f to the
corresponding value of (m f) in model *)
Definition unmap_model (m: FMap) (model: Model) : Model :=
  fun f => model (m f).

(* unmap_model on the identity map yields an equivalent model *)
Lemma unmap_model_id model :
  model_equiv model (unmap_model fmap_id model).
  intros f; reflexivity.
Qed.

(* unmap_model commutes with map composition *)
Lemma unmap_model_compose m2 m1 model :
  model_equiv (unmap_model m1 (unmap_model m2 model))
              (unmap_model (fmap_compose m2 m1) model).
  intros f. unfold unmap_model; reflexivity.
Qed.

(* The model_tail of unmap_model FIXME HERE *)
Lemma unmap_cons_equiv {l} fl f m model :
  ~@in_fl f l fl ->
  model_equiv_on fl (unmap_model m model) (unmap_model (fmap_cons f m) model).
  intros not_in f' i.
  unfold unmap_model; unfold fmap_cons.
  destruct (Field_dec_neq f f').
  intro e; apply not_in; rewrite e; assumption.
  rewrite e. reflexivity.
Qed.


(*** Proofs of equality to all elements in a list ***)

(* Construct the type t=t1 /\ ... /\ t=tn, where defs is [t1;...;tn] *)
Fixpoint eq_proofs {T} (t:T) (defs: list T) : Prop :=
  match defs with
    | nil => True
    | def::defs' => t = def /\ eq_proofs t defs'
  end.

(* Project the ith definition from a list of definitions, returning t if i is
bigger than the list *)
Definition proj_def {T t} i {defs} (pfs: eq_proofs t defs) : T :=
  nth i defs t.

(* Project the ith equality proof from a list of equality proofs *)
Fixpoint proj_eq_proof {T t} i defs {struct defs} : forall (pfs: eq_proofs t defs),
                                                      t = proj_def i pfs :=
  match defs return forall (pfs: eq_proofs t defs), t = proj_def i pfs with
    | nil =>
      fun pfs =>
        match i return t = @proj_def T t i nil pfs with
          | 0 => eq_refl t
          | S i' => eq_refl t
        end
    | def::defs' =>
      fun pfs =>
        match i return t = proj_def i pfs with
          | 0 => proj1 pfs
          | S i' => proj_eq_proof i' defs' (proj2 pfs)
        end
  end.


(*** Specs ***)

(* The inductive representation of specs, indexed by the op fields *)
Inductive SpecRepr : forall {l}, flist l -> Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : SpecRepr fnil
(* The inductive case adds an op named f with zero or more definitions to the
rest of the spec, that can depend on any f equal to all the definitions *)
| Spec_ConsOp f {l flds} not_in (T : Type) (defs: list T) (constraint: T -> Prop)
              (rest : forall t, eq_proofs t defs -> SpecRepr flds)
  : SpecRepr (@fcons f l not_in flds)
.

(* Make the field argument be parsed by Coq as a string *)
Arguments Spec_ConsOp f%string l flds not_in T defs constraint rest.

(* A bundled type for specs and their fields *)
Definition Spec : Type := {l:_ & {fl:_ & @SpecRepr l fl}}.

(* Extract the flist out of a Spec *)
Definition specFields (spec:Spec) := (projT1 (projT2 spec)).

(* Extract the representation out of a Spec *)
Definition specRepr (spec:Spec) := projT2 (projT2 spec).

(* Conjoin all the axioms in an axiom list *)
Definition conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_left (fun P1 f_P2 => and P1 (snd f_P2)) axioms True.

(* Whether a model satisfies a spec representation *)
Fixpoint satisfies_specRepr {l flds} (spec: @SpecRepr l flds) : Model -> Prop :=
  match spec in @SpecRepr l flds with
    | Spec_Axioms axioms => fun _ => conjoin_axioms axioms
    | Spec_ConsOp f not_in T defs constraint rest =>
      fun model =>
        exists (htim: has_type_in_model f T model)
               (eq_pfs: eq_proofs (model_proj f T model htim) defs),
          constraint (model_proj f T model htim) /\
          satisfies_specRepr (rest (model_proj f T model htim) eq_pfs) model
  end.

(* The bundled version of satsifeis_spec, operating on the Spec bundle type *)
Definition satisfies_spec (spec:Spec) model :=
  satisfies_specRepr (specRepr spec) model.

(* satisfies_spec is equivalent on equivalent models *)
Lemma satisfies_spec_equiv_on_models {l fl} (spec: @SpecRepr l fl) model1 model2 :
  model_equiv_on fl model1 model2 ->
  satisfies_specRepr spec model1 -> satisfies_specRepr spec model2.
  intros equiv sats; induction spec.
  assumption.
  destruct sats as [htim H0]; destruct H0 as [eq_pfs H0];
    destruct H0 as [constraint_pf sats].
  destruct (model_proj_equiv_f f T model1 model2 htim
                               (equiv f (in_fl_eq _ _ _))) as [htim' e2].
  exists htim'; rewrite <- e2.
  exists eq_pfs.
  split.
  assumption.
  apply (H _ _ (model_equiv_on_tail _ _ equiv)). assumption.
Qed.

(* satisfies_spec is equivalent on equivalent models *)
Lemma satisfies_spec_equiv_models {l fl} (spec: @SpecRepr l fl) model1 model2 :
  model_equiv model1 model2 ->
  satisfies_specRepr spec model1 -> satisfies_specRepr spec model2.
  intro equiv; apply satisfies_spec_equiv_on_models.
  apply model_equiv_on_any. assumption.
Qed.


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
  Spec_ConsOp "n" _ nat [] (fun _ => True)
              (fun n _ => Spec_Axioms [("gt1"%string, n > 1)]).

(* Example 2:  op n:nat := 2;  (no axioms) *)
Program Definition spec_repr_example_2 :=
  Spec_ConsOp "n" _ nat [2] (fun _ => True)
              (fun n _ => Spec_Axioms []).

(* Example 3:  op T:Set := nat;  op n:T__def;  axiom gt1: n > 1 *)
Program Definition spec_repr_example_3 :=
  Spec_ConsOp
    "T" _ Set [nat] (fun _ => True)
    (fun T T__eq_pfs =>
       Spec_ConsOp "n" _ (proj_def 0 T__eq_pfs) [] (fun _ => True)
                   (fun n _ => Spec_Axioms [("gt1"%string, n > 1)])).
Next Obligation.
intro. destruct H. discriminate. assumption.
Defined.

Print spec_repr_example_3.


(*** Morphisms ***)

(* m is a morphism from source to target iff it can unmap models of target into
models of source *)
Definition is_morphism {l_s fl_s l_t fl_t}
           (source: @SpecRepr l_s fl_s) (target: @SpecRepr l_t fl_t) m : Prop :=
  forall model,
    satisfies_specRepr target model ->
    satisfies_specRepr source (unmap_model m model).

(* A morphism from source to target is an m that is_morphism *)
Definition Morphism source target : Type :=
  { m | is_morphism (specRepr source) (specRepr target) m }.

(* The identity map on fl is a morphism from any spec on fl to itself *)
Lemma is_morphism_id spec : is_morphism (specRepr spec) (specRepr spec) fmap_id.
  unfold is_morphism; intros.
  apply (satisfies_spec_equiv_models _ _ _ (unmap_model_id model)).
  assumption.
Qed.

(* The identity morphism on spec *)
Definition morph_id (spec:Spec) : Morphism spec spec :=
  exist _ fmap_id (is_morphism_id spec).

(* Composing maps yields a morphism *)
Lemma is_morphism_compose (s3 s2 s1: Spec) m2 m1 :
  is_morphism (specRepr s2) (specRepr s3) m2 ->
  is_morphism (specRepr s1) (specRepr s2) m1 ->
  is_morphism (specRepr s1) (specRepr s3) (fmap_compose m2 m1).
  unfold is_morphism; intros ism2 ism1 model sats.
  apply (satisfies_spec_equiv_models _ _ _ (unmap_model_compose m2 m1 model)).
  apply ism1. apply ism2. assumption.
Qed.

(* The composition of two morphisms *)
Definition morph_compose {s3 s2 s1}
           (morph2: Morphism s2 s3) (morph1: Morphism s1 s2)
: Morphism s1 s3 :=
  exist _ (fmap_compose (proj1_sig morph2) (proj1_sig morph1))
        (is_morphism_compose s3 s2 s1 (proj1_sig morph2) (proj1_sig morph1)
                             (proj2_sig morph2) (proj2_sig morph1)).


(*** Morphisms on the tail of a spec ***)

(* A dependent spec is a spec inside a binder; note that the field list is not
inside the scope of the binder *)
Definition DepSpec T defs : Type :=
  {l:_ & {fl:_ & forall t:T, eq_proofs t defs -> @SpecRepr l fl}}.

(* Project out the SpecRepr of a DepSpec *)
Definition depSpecRepr {T defs} (spec: DepSpec T defs) :=
  projT2 (projT2 spec).

(* Add an op to the beginning of a DepSpec to get a Spec *)
Definition depSpec_ConsOp f T defs constraint (spec: DepSpec T defs) not_in : Spec :=
  existT _ _ (existT _ _ (Spec_ConsOp f not_in T defs constraint (depSpecRepr spec))).

(* A dependent morphism is morphism inside a binder; note that the mapping is
not inside the scope of the binder *)
Definition DepMorphism {T defs} (source target: DepSpec T defs) :=
  { m | forall t eq_pfs, is_morphism (depSpecRepr source t eq_pfs)
                                     (depSpecRepr target t eq_pfs) m }.

(* A morphism on the tail of two specs extendeds to one on the full specs *)
Lemma is_morphism_cons f T defs constraint (source target: DepSpec T defs) not_in_s not_in_t m :
  (forall t eq_pfs, is_morphism (depSpecRepr source t eq_pfs)
                                (depSpecRepr target t eq_pfs) m) ->
  is_morphism (Spec_ConsOp f not_in_s T defs constraint (depSpecRepr source))
              (Spec_ConsOp f not_in_t T defs constraint (depSpecRepr target))
              (fmap_cons f m).
  intros ism model sats.
  destruct sats as [htim H]; destruct H as [eq_pfs H];
    destruct H as [constraint_pf sats].
  destruct (model_proj_equiv_f f T _ (unmap_model (fmap_cons f m) model) htim)
    as [htim' proj_eq].
  unfold unmap_model; unfold fmap_cons.
  destruct (Field_dec_eq f) as [e1 e2]; rewrite e2; reflexivity.
  exists htim'.
  rewrite <- proj_eq.
  exists eq_pfs.
  split.
  assumption.
  apply (satisfies_spec_equiv_on_models
           _ _ _
           (unmap_cons_equiv _ _ _ _ not_in_s)).
  apply ism.
  assumption.
Qed.

(* Cons an op onto the front of a dependent morphism *)
Definition morph_cons f {T} defs constraint {s1 s2} not_in1 not_in2
           (morph : @DepMorphism T defs s1 s2) :
  Morphism (depSpec_ConsOp f T defs constraint s1 not_in1)
           (depSpec_ConsOp f T defs constraint s2 not_in2) :=
  exist _ (fmap_cons f (proj1_sig morph))
        (is_morphism_cons f T _ _ _ _ not_in1 not_in2
                          (proj1_sig morph) (proj2_sig morph)).


(*** Transformations ***)

(* The top-level proof goal of a transformation is always RefinementOf spec *)
Definition RefinementOf (spec:Spec) : Type :=
  {spec' : Spec & Morphism spec spec'}.
