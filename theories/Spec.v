
(*** Modeling specs and morphisms as Coq terms ***)

Require Import List.
Import ListNotations.
Require Import String.

(*
Add LoadPath "." as Specware.
Require Import Specware.Util.
*)


(* Define the type of fields in one place, so we can change it later *)

Definition Field : Set := string.
Definition Field_dec : forall (f1 f2 : Field), {f1=f2} + {f1<>f2} := string_dec.


(*** The inductive type of specs ***)

Inductive Spec : Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop))
(* Declared op: the rest of the spec can refer to the op *)
| Spec_DeclOp (f : Field) (T : Type) (rest : T -> Spec)
(* Defined op: gives an element of the type *)
| Spec_DefOp (f : Field) (T : Type) (t : T) (rest : Spec)
.

(*
Inductive Spec : list string -> Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : Spec []
(* Declared op: the rest of the spec can refer to the op *)
| Spec_DeclOp flds f (T : Type) (rest : T -> Spec flds)
  : Spec (f :: flds)
(* Defined op: gives an element of the type *)
| Spec_DefOp flds f (T : Type) (t : T) (rest : Spec flds)
  : Spec (f :: flds)
.
*)

(*** The models of a spec ***)

Definition Any : Type := { T : Type & T }.
Definition mkAny (T:Type) (t:T) : Any := existT (fun T => T) T t.
Definition dummyAny : Any := mkAny _ tt.

Definition Model := list (Field * Any).

Fixpoint model_proj f model : option Any :=
  match model with
    | [] => None
    | (f', any) :: model' =>
      if Field_dec f f' then Some any else
        model_proj f model'
  end.

Fixpoint combine_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_left (fun P1 f_P2 => and P1 (snd f_P2)) axioms True.

(* NOTE: this is in Type because we need to compute the model elements *)
Fixpoint IsModel (model:Model) (s:Spec) : Prop :=
  match s with
    | Spec_Axioms axioms => combine_axioms axioms
    | Spec_DeclOp f T rest =>
      exists t, model_proj f model = Some (mkAny T t) /\ IsModel model (rest t)
    | Spec_DefOp f T t rest =>
      model_proj f model = Some (mkAny T t) /\ IsModel model rest
  end.


(*** Field maps ***)

Definition FMap := list (Field * Field).

(*
Definition FMap := { l : list (Field * Field) | NoDup (map fst l) }.

Lemma NoDup_tail A (x:A) l : NoDup (x::l) -> NoDup l.
  intro nd. apply (NoDup_remove_1 [] l x). assumption.
Qed.
*)

Fixpoint apply_fmap (m : FMap) (f : Field) : Field :=
  match m with
    | [] => f
    | (f_in, f_out) :: m' =>
      if Field_dec f f_in then f_out else apply_fmap m' f
  end.

Definition fmap_id : FMap := [].

Lemma fmap_id_ok f : apply_fmap fmap_id f = f.
  reflexivity.
Qed.

Fixpoint fmap_compose (m2 m1 : FMap) : FMap :=
  match m1 with
    | [] => m2
    | (f_in, f_out) :: m1' =>
      (f_in, apply_fmap m2 f_out) :: fmap_compose m2 m1'
  end.

Lemma fmap_compose_ok m2 m1 f :
  apply_fmap (fmap_compose m2 m1) f = apply_fmap m2 (apply_fmap m1 f).
  induction m1.
  reflexivity.
  destruct a.
  unfold apply_fmap; unfold fmap_compose; fold fmap_compose; fold apply_fmap.
  destruct (Field_dec f f0).
  reflexivity.
  assumption.
Qed.

Definition fmap_dom (m : FMap) : list Field := map fst m.

Lemma reverse_fmap m f1 f2 :
  apply_fmap m f1 = f2 -> f1 = f2 \/ In f1 (fmap_dom m).
  admit. (* FIXME HERE *)
Qed.


(*** Morphisms ***)

Fixpoint unmap_model (m : FMap) (model:Model) : Model := FIXME HERE

Fixpoint IsMappedModel (m : FMap) (model:Model) (s:Spec) : Prop :=
  match s with
    | Spec_Axioms axioms => combine_axioms axioms
    | Spec_DeclOp f T rest =>
      exists t,
        model_proj (apply_fmap m f) model = Some (mkAny T t)
        /\ IsMappedModel m model (rest t)
    | Spec_DefOp f T t rest =>
      model_proj (apply_fmap m f) model = Some (mkAny T t)
      /\ IsMappedModel m model rest
  end.

Definition IsMorphism m (source target : Spec) : Prop :=
  forall model, IsModel model target -> IsMappedModel m model source.


Lemma IsMappedModel_id model s : IsModel model s <-> IsMappedModel fmap_id model s.
  split; induction s;
  unfold IsModel; fold IsModel; unfold IsMappedModel; fold IsMappedModel; intro.
  assumption.
  destruct H0; destruct H0; exists x; split; [ | apply H]; assumption.
  destruct H; split; [ | apply IHs ]; assumption.
  assumption.
  destruct H0; destruct H0; exists x; split; [ | apply H]; assumption.
  destruct H; split; [ | apply IHs ]; assumption.
Qed.

Theorem morphism_refl spec : IsMorphism fmap_id spec spec.
  intros model ism; apply IsMappedModel_id; assumption.
Qed.

(* Need a model (or a mapped model) to extract the fields from a spec *)
(* Argh, needs UIP! *)
(*
Definition spec_fields m model spec : IsMappedModel m model spec -> list Field.
  induction spec; unfold IsMappedModel; fold IsMappedModel; intro ism.
  exact [].
  destruct (model_proj (m f) model).
  destruct a. assert (x = T).
  destruct ism; destruct H; injection H; intros; assumption.
  revert p ism; rewrite H; intros.
  assert (IsMappedModel m model (rest p)).
  destruct ism; 
*)
(*
Fixpoint spec_fields m model spec : IsMappedModel m model spec -> list Field :=
  match spec with
    | Spec_Axioms _ => fun _ => []
    | Spec_DeclOp f T rest =>
*)


Definition unmap_model (m : Field -> Field) (model:Model) (s:Spec) :
  IsMappedModel m model s -> {model' | IsModel model' s }.
  induction s; unfold IsMappedModel; fold IsMappedModel;
  unfold IsModel; fold IsModel; intro ism.
  exists []; assumption.
  case_eq (model_proj (m f) model); intros.
  destruct a. assert (x = T).
  destruct ism; destruct H0; rewrite H in H0;
    injection H0; intros; assumption.
  revert p H; rewrite H0; intros.
  destruct (X p).
  

  exists (m f, a).


Fixpoint unmap_model (m : Field -> Field) (model:Model) (s:Spec) :
  IsMappedModel m model s -> Model :=
  match s with
    | Spec_Axioms axioms => fun _ => x[]
    | Spec_DeclOp f T rest =>
      fun ism =>


(*** FIXME: Old stuff below... ***)

Fixpoint spec_model (spec:Spec) : Type :=
  match spec with
    | Spec_Axioms axioms =>
      combine_axioms axioms
    | Spec_DeclOp _ T rest =>
      { t : T & spec_model (rest t)}
    | Spec_DefOp _ _ _ rest => spec_model rest
  end.


(*** Project an op from a model of a spec ***)

Fixpoint model_proj f spec : spec_model spec -> { T : Type & T } :=
  match spec  with
    | Spec_Axioms _ => fun _ => existT (fun T => T) unit tt
    | Spec_DeclOp f' T rest =>
      fun model =>
        if Field_dec f f' then (existT (fun T => T) T (projT1 model))
      else model_proj f (rest (projT1 model)) (projT2 model)
    | Spec_DefOp f' T t rest =>
      fun model =>
        if Field_dec f f' then existT _ T t
        else model_proj f rest model
  end.


(*** Whether a field function defines a morphism ***)

(* Note: the co-domain comes first in IsMorphism, because it does not vary *)
(*
Inductive IsMorphism (m : Field -> Field) (s_codom : Spec) : Spec -> Prop :=
| IsMorphism_Axioms 
*)

Fixpoint IsMorphModel (m : Field -> Field)
         (source target : Spec) (t_model : Model) : Prop :=
  match source with
    | Spec_Axioms axioms =>
      combine_axioms axioms
    | Spec_DeclOp f T rest =>
      

Fixpoint IsMorphism (m : Field -> Field) (source target : Spec) : Prop :=
  match source with
    | Spec_Axioms axioms =>
      combine_axioms axioms
    | Spec_DeclOp f T rest =>
