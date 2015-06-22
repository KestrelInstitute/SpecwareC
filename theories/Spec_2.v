
(*** Modeling specs and morphisms as Coq terms ***)

Require Import List.
Import ListNotations.
Require Import String.

(*
Add LoadPath "." as Specware.
Require Import Specware.Util.
*)


(*** Fields and Field Maps ***)

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


(* A field map is an association list on fields *)
Definition FMap := list (Field * Field).

(*
Definition FMap := { l : list (Field * Field) | NoDup (map fst l) }.

Lemma NoDup_tail A (x:A) l : NoDup (x::l) -> NoDup l.
  intro nd. apply (NoDup_remove_1 [] l x). assumption.
Qed.
*)

(* Apply a field map to a field *)
Fixpoint apply_fmap (m : FMap) (f : Field) : Field :=
  match m with
    | [] => f
    | (f_in, f_out) :: m' =>
      if Field_dec f f_in then f_out else apply_fmap m' f
  end.

(* The identity field map *)
Definition fmap_id : FMap := [].

(* fmap_id is the identity *)
Lemma fmap_id_ok f : apply_fmap fmap_id f = f.
  reflexivity.
Qed.

(* Compose two field maps *)
Fixpoint fmap_compose (m2 m1 : FMap) : FMap :=
  match m1 with
    | [] => m2
    | (f_in, f_out) :: m1' =>
      (f_in, apply_fmap m2 f_out) :: fmap_compose m2 m1'
  end.

(* Field map composition commutes with application *)
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

(* The domain of a field map *)
Definition fmap_dom (m : FMap) : list Field := map fst m.

(* Inversion lemma for field maps *)
(*
Lemma reverse_fmap m f1 f2 :
  apply_fmap m f1 = f2 -> f1 = f2 \/ In f1 (fmap_dom m).
  admit. (* FIXME HERE *)
Qed.
*)


(*** Field lists, with no duplicates ***)

Definition flist := { l : list Field | NoDup l }.

Definition fnil : flist := exist _ [] (NoDup_nil Field).

Definition fcons f l (pf : ~ In f (proj1_sig l)) : flist :=
  exist _ (f :: proj1_sig l) (NoDup_cons f pf (proj2_sig l)).

Definition in_fl f (l : flist) : Prop := In f (proj1_sig l).

Definition in_fl_dec f l : {in_fl f l} + {~ in_fl f l} :=
  In_dec Field_dec f (proj1_sig l).

Lemma in_fl_eq f l pf : in_fl f (fcons f l pf).
  left; reflexivity.
Qed.

Lemma in_fl_fcons_inv f f' l pf : in_fl f (fcons f' l pf) -> f' <> f -> in_fl f l.
  unfold in_fl; intros; destruct H.
    elimtype False; apply (H0 H).
    assumption.
Qed.

Definition in_fl_inv f f' l pf (i: in_fl f (fcons f' l pf)) : {f'=f} + {in_fl f l} :=
  match Field_dec f' f with
    | left e => left e
    | right neq => right (in_fl_fcons_inv _ _ _ _ i neq)
  end.


(*** The inductive type of specs ***)

(* The type of something that "completes" an option type if it is None, or is a
unit if the option is Some *)
Definition unopt T (t_opt : option T) : Type :=
  if t_opt then unit else T.

Definition unopt_combine T t_opt : unopt T t_opt -> T :=
  match t_opt return unopt T t_opt -> T with
    | Some t => fun _ => t
    | None => fun t => t
  end.

Inductive Spec : flist -> Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : Spec fnil
(* The recursive case adds an op with an optional definition *)
| Spec_ConsOp f flds not_in (T : Type) (t_opt : option T)
            (rest : unopt T t_opt -> Spec flds)
  : Spec (fcons f flds not_in)
.


(*** The Models of a Spec ***)

(* Helper for elements of a model at an arbitrary type *)
Definition Any : Type := { T : Type & T }.
Definition mkAny (T:Type) (t:T) : Any := existT (fun T => T) T t.

(* Helper for conjoining all the axioms in an axiom list *)
Fixpoint conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_left (fun P1 f_P2 => and P1 (snd f_P2)) axioms True.

(* Build the type of the models of spec as a nested dependent pair *)
Fixpoint spec_model flds (spec:Spec flds) : Type :=
  match spec in Spec flds with
    | Spec_Axioms axioms =>
      conjoin_axioms axioms
    | Spec_ConsOp _ flds' _ T t_opt rest =>
      { t : unopt T t_opt & spec_model flds' (rest t)}
  end.

(* Whether field f has type T in a model *)
Fixpoint has_type_in_model f T flds spec : spec_model flds spec -> Prop :=
  match spec in Spec flds return spec_model flds spec -> Prop with
    | Spec_Axioms _ => fun model => False
    | Spec_ConsOp f' flds' not_in T' t_opt' rest =>
      fun model =>
        (f = f' -> T' = T) /\
        (f <> f' ->
         has_type_in_model f T flds' (rest (projT1 model)) (projT2 model))
  end.

Lemma has_type_in_model_in_flds f T flds spec model :
  has_type_in_model f T flds spec model -> in_fl f flds.
  revert model; induction spec; intros.
  elimtype False; apply H.
  destruct (Field_dec f f0).
  rewrite e; apply in_fl_eq.
  right. apply (H (projT1 model) (projT2 model)).
  destruct H0. apply H1. assumption.
Qed.

Lemma has_type_in_model_eq f T flds not_in t_opt rest model :
  has_type_in_model f T _ (Spec_ConsOp f flds not_in T t_opt rest) model.
  destruct t_opt; (split; intros; [ | elimtype False; apply H ]; reflexivity).
Qed.

Lemma has_type_in_model_cons f T f' flds' not_in T' t_opt' rest t_opt model
: f <> f' -> has_type_in_model f T flds' (rest t_opt) model ->
  has_type_in_model f T _ (Spec_ConsOp f' flds' not_in T' t_opt' rest)
                    (existT _ t_opt model).
  split; [ intro H1; elimtype False; apply (H H1) | ].
  intros; assumption.
Qed.


(* Project a field out of a model of a spec *)
Fixpoint model_proj f T flds spec
: forall model, has_type_in_model f T flds spec model -> T :=
  match spec in Spec flds
        return forall model, has_type_in_model f T flds spec model -> T with
    | Spec_Axioms _ => fun model htim => (match htim with end)
    | Spec_ConsOp f' flds' not_in T' t_opt' rest =>
      fun model htim =>
        match Field_dec f f' with
          | left e => eq_rect T' id (unopt_combine _ _ (projT1 model)) T
                              ((match htim with conj f _ => f end) e)
          | right neq =>
            model_proj f T flds' (rest (projT1 model)) (projT2 model)
                       ((match htim with conj _ f => f end) neq)
        end
  end.


(*** Model Substitution ***)

(* This is true iff a model of source can be built from a given model of target
by using field map m to map each field of source to one of target. *)
Fixpoint CanSubstModel (m : FMap) flds_s (source : Spec flds_s) flds_t
         (target : Spec flds_t) (model : spec_model _ target) : Prop :=
  match source in Spec flds_s with
    | Spec_Axioms axioms => conjoin_axioms axioms
    | Spec_ConsOp f flds_s' not_in T t_opt rest =>
      exists (htim : has_type_in_model (apply_fmap m f) T flds_t target model),
        CanSubstModel m flds_s' (rest (model_proj _ _ _ _ model htim)) flds_t target model
  end.
