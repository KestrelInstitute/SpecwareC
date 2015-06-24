
(*** Modeling specs and morphisms as Coq terms ***)

Require Import List.
Import ListNotations.
Require Import String.
Import EqNotations.
Require Export Coq.Logic.Eqdep_dec.

(*
Add LoadPath "." as Specware.
Require Import Specware.Util.
*)


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
  Check NoDup_remove_2.
  elimtype False; apply (NoDup_remove_2 [] l a nd); rewrite e; assumption.
  elimtype False; apply (NoDup_remove_2 [] l a nd); rewrite e; assumption.
  f_equal; apply (IHl (NoDup_remove_1 [] l a nd)).
Qed.


(* A field in a field list *)
Definition Field_in {l} fl : Set := { f : Field | @in_fl f l fl }.

(* Helper for building Field_in's *)
Definition mk_Field_in {l} fl f in_fl : @Field_in l fl := exist _ f in_fl.

(* Cons onto the field list that a Field_in is in *)
Definition Field_in_cons f' {l fl not_in} (f: Field_in fl) :
  Field_in (@fcons f' l not_in fl) :=
  mk_Field_in _ (proj1_sig f) (in_fl_cons (proj1_sig f) (proj2_sig f)).

(* Build a Field_in f (fcons f not_in fl) *)
Definition mk_Field_in_cons f {l} fl not_in : Field_in (@fcons f l not_in fl) :=
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


(*** Models ***)

(* Helper for elements of a model at an arbitrary type *)
Definition Any : Type := { T : Type & T }.
Definition mkAny (T:Type) (t:T) : Any := existT (fun T => T) T t.
Definition anyType (any:Any) : Type := projT1 any.
Definition anyObj (any:Any) : anyType any := projT2 any.

(* A model is maps fields in a field list to ops for those fields *)
Definition Model {l} (fl : flist l) : Type :=
  Field_in fl -> Any.

(* Whether f has type T in model *)
Definition has_type_in_model {l fl} f T (model: @Model l fl) : Prop :=
  anyType (model f) = T.

(* Project field f from model *)
Definition model_proj {l fl} f T (model: @Model l fl)
         (htim: has_type_in_model f T model) : T :=
  rew [id] htim in (anyObj (model f)).

(* Build a model with a subset of the fields in flds by mapping each f to the
corresponding value of (m f) in model *)
Definition unmap_model {sl s tl t} (m : @FMap sl s tl t)
           (model: Model t) : Model s :=
  fun f => model (apply_fmap m f).

(* Take a sub-model, removing the first element *)
Definition model_tail {f l fl not_in}
           (model: Model (@fcons f l not_in fl)) : Model fl :=
  fun f' => model (Field_in_cons f f').


(*** Specs ***)

Inductive Spec : forall {l}, flist l -> Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : Spec fnil
(* Declared op: the rest of the spec can refer to the op *)
| Spec_DeclOp f {l} flds not_in (T : Type) (rest : T -> Spec flds)
  : Spec (@fcons f l not_in flds)
(* Defined op: gives an element of the type *)
| Spec_DefOp f {l} flds not_in (T : Type) (t : T) (rest : Spec flds)
  : Spec (@fcons f l not_in flds)
.

(* Conjoin all the axioms in an axiom list *)
Definition conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_left (fun P1 f_P2 => and P1 (snd f_P2)) axioms True.

(* Whether a model satisfies a spec *)
Fixpoint satisfies_spec {l flds} (spec: @Spec l flds) : Model flds -> Prop :=
  match spec in @Spec l flds return Model flds -> Prop with
    | Spec_Axioms axioms => fun _ => conjoin_axioms axioms
    | Spec_DeclOp f flds' not_in T rest =>
      fun model =>
        exists (htim: has_type_in_model
                        (mk_Field_in_cons f flds' not_in) T model),
          satisfies_spec
            (rest (model_proj _ T model htim))
            (model_tail model)
    | Spec_DefOp f flds' not_in T t rest =>
      fun model =>
        (exists (htim: has_type_in_model
                         (mk_Field_in_cons f flds' not_in) T model),
           model_proj _ T model htim = t) /\
        satisfies_spec rest (model_tail model)
  end.


(*** Morphisms ***)

Definition IsMorphism {sl s tl t} (m: @FMap sl s tl t) (source: Spec s) (target : Spec t) : Prop :=
  forall model,
    satisfies_spec target model ->
    satisfies_spec source (unmap_model m model).

Lemma is_morphism_id l fl spec : IsMorphism (@fmap_id l fl) spec spec.
  unfold IsMorphism; unfold unmap_model; induction spec; intros.
  assumption.
  destruct H0 as [htim H0]. exists htim. apply H. assumption.
  destruct H as [H H0]; destruct H as [htim H]. split.
  exists htim. assumption.
  apply IHspec. assumption.
Qed.
