
(*** Modeling specs and morphisms as Coq terms ***)

(* This approach defines models as functions from fields in a given list *)

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

(* A field in a field list *)
Definition Field_in {l} fl : Set := { f : Field | @in_fl f l fl }.

(* Helper for building Field_in's *)
Definition mk_Field_in {l} fl f in_fl : @Field_in l fl := exist _ f in_fl.

(* Cons onto the field list that a Field_in is in *)
Definition Field_in_cons f' {l fl not_in} (f: Field_in fl) :
  Field_in (@fcons f' l not_in fl) :=
  mk_Field_in _ (proj1_sig f) (in_fl_cons (proj1_sig f) (proj2_sig f)).

(* Remove the head of the field list that a Field_in is in *)
Definition Field_in_tail {f' l not_in fl} (f: Field_in (@fcons f' l not_in fl))
           (neq: proj1_sig f <> f') : Field_in fl :=
  exist _ (proj1_sig f) (in_fl_tail _ neq (proj2_sig f)).

(* Build a Field_in f (fcons f not_in fl) *)
Definition Field_in_eq f {l} not_in fl : Field_in (@fcons f l not_in fl) :=
  mk_Field_in _ f (in_fl_eq f not_in fl).

(* Decidable equaltiy on Field_in *)
Definition Field_in_dec {l} fl (f1 f2 : @Field_in l fl) : {f1=f2} + {f1 <> f2}.
  destruct f1 as [f1 in1]; destruct f2 as [f2 in2]; destruct (Field_dec f1 f2).
  revert in1 in2; rewrite e; intros; left;
    f_equal; apply in_fl_uniq; apply flist_NoDup; assumption.
  right. injection. assumption.
Qed.

Lemma Field_in_dec_eq {l} fl f1 pf1 f2 pf2
: f1 = f2 -> { e | @Field_in_dec l fl (exist _ f1 pf1) (exist _ f2 pf2) = left e }.
  intro e; destruct (Field_in_dec fl (exist _ f1 pf1) (exist _ f2 pf2)).
  exists e0; reflexivity.
  revert pf1 pf2 n; rewrite e; intros.
  elimtype False; apply n; f_equal;
    apply in_fl_uniq; apply flist_NoDup; assumption.
Qed.

Lemma Field_in_dec_neq {l} fl f1 pf1 f2 pf2
: f1 <> f2 -> { neq | @Field_in_dec l fl (exist _ f1 pf1) (exist _ f2 pf2) = right neq }.
  intro neq; destruct (Field_in_dec fl (exist _ f1 pf1) (exist _ f2 pf2)).
  elimtype False; apply neq; injection e; intros; assumption.
  exists n; reflexivity.
Qed.


(*** The category of field maps on field lists ***)

(* A field map is a field function with a specified domain and codomain *)
Definition FMap {sl} (source : flist sl) {tl} (target : flist tl) :=
  Field_in source -> Field_in target.

Definition apply_fmap {sl s tl t} (m : @FMap sl s tl t)
           (f : Field_in s) : Field_in t := m f.

(* Build the identity field map *)
Definition fmap_id {l} fl : @FMap l fl l fl := fun f => f.

(* Applying fmap_id is the identity *)
Lemma fmap_id_is_id l fl f : apply_fmap (@fmap_id l fl) f = f.
  reflexivity.
Qed.

(* Compose two field map alists *)
Definition fmap_compose {l3 fl3 l2 fl2 l1 fl1} (m2 : @FMap l2 fl2 l3 fl3)
         (m1 : @FMap l1 fl1 l2 fl2) : FMap fl1 fl3 :=
  fun f => m2 (m1 f).

(* Field map composition commutes with application *)
Lemma fmap_compose_composes l3 fl3 l2 fl2 l1 fl1 (m2 : FMap fl2 fl3) (m1 : FMap fl1 fl2) f :
  apply_fmap (@fmap_compose l3 fl3 l2 fl2 l1 fl1 m2 m1) f
  = apply_fmap m2 (apply_fmap m1 f).
  reflexivity.
Qed.

(* Cons an op onto the source of a field map *)
Definition fmap_cons {l1 fl1 l2 fl2} f not_in1 not_in2 (m: @FMap l1 fl1 l2 fl2) :
  FMap (fcons f not_in1 fl1) (fcons f not_in2 fl2) :=
  fun f' =>
    match Field_dec (proj1_sig f') f with
      | left _ => Field_in_eq f not_in2 fl2
      | right neq => Field_in_cons f (m (Field_in_tail f' neq))
    end.


(*** Models ***)

(* Helper for elements of a model at an arbitrary type *)
Definition Any : Type := { T : Type & T }.
Definition mkAny (T:Type) (t:T) : Any := existT (fun T => T) T t.
Definition anyType (any:Any) : Type := projT1 any.
Definition anyObj (any:Any) : anyType any := projT2 any.

(* A model is maps fields in a field list to ops for those fields *)
Definition Model {l} (fl : flist l) : Type :=
  Field_in fl -> Any.

(* Model equivalence is extensional equality (without needing an axiom) *)
Definition model_equiv {l fl} (model1 model2 : @Model l fl) : Prop :=
  forall f, model1 f = model2 f.

(* Whether f has type T in model *)
Definition has_type_in_model {l fl} f T (model: @Model l fl) : Prop :=
  anyType (model f) = T.

(* has_type_in_model is equal in equivalent models *)
Lemma has_type_in_model_equiv {l fl} f T model1 model2 :
  @model_equiv l fl model1 model2 ->
  has_type_in_model f T model1 = has_type_in_model f T model2.
  intros equiv; unfold has_type_in_model; rewrite <- (equiv f); reflexivity.
Qed.

(* Project field f from model *)
Definition model_proj {l fl} f T (model: @Model l fl)
         (htim: has_type_in_model f T model) : T :=
  rew [id] htim in (anyObj (model f)).

(* model_proj is equal (modulo htim proof) in equivalent models *)
Lemma model_proj_equiv {l fl} f T model1 model2 htim
      (equiv: @model_equiv l fl model1 model2) :
  exists htim', model_proj f T model1 htim = model_proj f T model2 htim'.
  unfold model_proj; unfold has_type_in_model.
  rewrite <- (equiv f). exists htim. reflexivity.
Qed.

(* Take a sub-model, removing the first element *)
Definition model_tail {f l fl not_in}
           (model: Model (@fcons f l not_in fl)) : Model fl :=
  fun f' => model (Field_in_cons f f').

(* model_tail preserves equivalence *)
Definition model_tail_equiv {f l fl not_in}
           (model1 model2 : Model (@fcons f l not_in fl)) :
  model_equiv model1 model2 ->
  model_equiv (model_tail model1) (model_tail model2).
  unfold model_equiv; unfold model_tail; intros equiv f'.
  apply equiv.
Qed.

(* Build a model with a subset of the fields in flds by mapping each f to the
corresponding value of (m f) in model *)
Definition unmap_model {sl s tl t} (m : @FMap sl s tl t)
           (model: Model t) : Model s :=
  fun f => model (apply_fmap m f).

(* unmap_model on the identity map yields an equivalent model *)
Lemma unmap_model_id l fl model :
  model_equiv model (unmap_model (@fmap_id l fl) model).
  intro f; unfold unmap_model; rewrite fmap_id_is_id; reflexivity.
Qed.

(* unmap_model commutes with map composition *)
Lemma unmap_model_compose {l3 fl3 l2 fl2} (m2: @FMap l2 fl2 l3 fl3)
      {l1 fl1} (m1: @FMap l1 fl1 l2 fl2) model :
  model_equiv (unmap_model m1 (unmap_model m2 model))
              (unmap_model (fmap_compose m2 m1) model).
  intro f; unfold unmap_model; rewrite fmap_compose_composes; reflexivity.
Qed.

(* The model_tail of unmap_model FIXME HERE *)



(*** Specs ***)

(* The inductive representation of specs, indexed by the op fields *)
Inductive SpecRepr : forall {l}, flist l -> Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : SpecRepr fnil
(* Declared op: the rest of the spec can refer to the op *)
| Spec_DeclOp f {l flds} not_in (T : Type) (rest : T -> SpecRepr flds)
  : SpecRepr (@fcons f l not_in flds)
(* Defined op: gives an element of the type *)
| Spec_DefOp f {l flds} not_in (T : Type) (t : T) (rest : SpecRepr flds)
  : SpecRepr (@fcons f l not_in flds)
.

(* Make the field argument be parsed by Coq as a string *)
Arguments Spec_DeclOp f%string l flds not_in T rest.
Arguments Spec_DefOp f%string l flds not_in T t rest.

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
Fixpoint satisfies_specRepr {l flds} (spec: @SpecRepr l flds) : Model flds -> Prop :=
  match spec in @SpecRepr l flds return Model flds -> Prop with
    | Spec_Axioms axioms => fun _ => conjoin_axioms axioms
    | Spec_DeclOp f not_in T rest =>
      fun model =>
        exists (htim: has_type_in_model
                        (Field_in_eq f not_in _) T model),
          satisfies_specRepr
            (rest (model_proj _ T model htim))
            (model_tail model)
    | Spec_DefOp f not_in T t rest =>
      fun model =>
        (exists (htim: has_type_in_model
                         (Field_in_eq f not_in _) T model),
           model_proj _ T model htim = t) /\
        satisfies_specRepr rest (model_tail model)
  end.

(* The bundled version of satsifeis_spec, operating on the Spec bundle type *)
Definition satisfies_spec (spec:Spec) model :=
  satisfies_specRepr (specRepr spec) model.

(* satisfies_spec is equivalent on equivalent models *)
Lemma satisfies_spec_equiv_models {l fl} (spec: @SpecRepr l fl) model1 model2 :
  model_equiv model1 model2 ->
  satisfies_specRepr spec model1 -> satisfies_specRepr spec model2.
  intros equiv sats; induction spec.
  assumption.
  destruct sats as [htim sats'].
  destruct (model_proj_equiv (Field_in_eq f not_in flds)
                             T model1 model2 htim equiv) as [htim' e].
  exists htim'; rewrite <- e.
  apply (H _ _ _ (model_tail_equiv _ _ equiv)). assumption.
  destruct sats as [H sats']; destruct H as [htim e].
  split.
  destruct (model_proj_equiv (Field_in_eq f not_in flds)
                             T model1 model2 htim equiv) as [htim' e2].
  exists htim'; rewrite <- e2; assumption.
  apply (IHspec _ _ (model_tail_equiv _ _ equiv)).
  assumption.
Qed.

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

(* An example *)
Program Definition spec_repr_example_1 :=
  Spec_DeclOp "n" _ nat
              (fun n => Spec_Axioms [("gt1"%string, n > 1)]).


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
Lemma is_morphism_id spec : is_morphism (specRepr spec) (specRepr spec) (fmap_id _).
  unfold is_morphism; intros.
  apply (satisfies_spec_equiv_models _ _ _ (unmap_model_id _ _ model)).
  assumption.
Qed.

(* The identity morphism on spec *)
Definition morph_id (spec:Spec) : Morphism spec spec :=
  exist _ (fmap_id _) (is_morphism_id spec).

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

(* A morphism on the tail of two specs extendeds to one on the full specs *)
Lemma is_morphism_cons_decl f T {l_s fl_s l_t fl_t} not_in_s not_in_t
           (source: T -> @SpecRepr l_s fl_s) (target: T -> @SpecRepr l_t fl_t)
           (m: FMap fl_s fl_t) :
  (forall t, is_morphism (source t) (target t) m) ->
  is_morphism (Spec_DeclOp f not_in_s T source)
              (Spec_DeclOp f not_in_t T target)
              (fmap_cons f not_in_s not_in_t m).
  intros ism model sats.
  destruct sats as [htim sats].
  assert (has_type_in_model (Field_in_eq f not_in_s fl_s) T
                            (unmap_model (fmap_cons f not_in_s not_in_t m) model))
    as htim'.
  unfold has_type_in_model; unfold unmap_model; unfold apply_fmap; unfold fmap_cons;
    unfold Field_in_eq at 1; unfold mk_Field_in; unfold proj1_sig.
  destruct (Field_dec_eq f) as [e1 e2]; rewrite e2; assumption.
  exists htim'.
  unfold unmap_model; unfold model_proj.
  

  apply (ism).

  unfold unmap_model; unfold model_proj.


  exists htim.

  econstructor. Check ?htim.


  unfold satisfies_specRepr. unfold has_type_in_model. unfold unmap_model.

  exists eq_refl.


(*** Transformations ***)

(* The top-level proof goal of a transformation is always RefinementOf spec *)
Definition RefinementOf (spec:Spec) : Type :=
  {spec' : Spec & Morphism spec spec'}.
