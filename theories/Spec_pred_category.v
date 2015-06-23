
(*** Modeling specs and morphisms as Coq terms ***)

(* This approach attempts to model field maps as morphisms in a category of
non-duplicated field lists. I got stuck on the complexity of flist_rect_H,
below... *)

Require Import List.
Import ListNotations.
Require Import String.
Import EqNotations.

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

(* Injectivity of cons *)
Lemma cons_inj A (x1:A) l1 x2 l2 : x1::l1 = x2::l2 -> x1 = x2 /\ l1 = l2.
  intros; injection H; intros; split; assumption.
Qed.

FIXME HERE: the following requires axiom K for field lists (which is provable but annoying...)

(* Recursion scheme for flists *)
Fixpoint flist_rect_H
         (P : flist -> Type) (f1 : P fnil)
         (f2 : forall f l not_in, P l -> P (fcons f l not_in))
         l : forall nd, P (exist _ l nd) :=
  match l return forall nd, P (exist _ l nd) with
    | [] => fun nd => f1
    | f::l' =>
      fun nd =>
      f2 f (exist _ l' (NoDup_remove_2 [] l' f nd))

(* A field in a field list *)
Definition Field_in fl : Set := { f : Field | in_fl f fl }.


(*** The category of field maps on field lists ***)

(* The type of field maps from source to target *)
Inductive FMap (target : flist) : flist -> Set :=
| FMap_nil : FMap target fnil
| FMap_cons (f_to : Field_in target) source f_from not_in_s :
    FMap target source -> FMap target (fcons f_from source not_in_s)
.

(* Apply a field map to a field *)
Fixpoint apply_fmap_field s t (m : FMap t s) (f : Field) : Field := 
  match m with
    | FMap_nil _ => f
    | FMap_cons _ f_to s' f_from not_in m' =>
      if Field_dec f f_from then proj1_sig f_to else apply_fmap_field s' t m' f
  end.

(* Applying a field map goes from fields in s to fields in t *)
Lemma apply_fmap_proof s t (m : FMap t s) f :
  in_fl f s -> in_fl (apply_fmap_field s t m f) t.
  induction m; intros.
  elimtype False; assumption.
  unfold apply_fmap_field; fold apply_fmap_field; destruct (Field_dec f f_from).
  apply (proj2_sig f_to).
  apply IHm; destruct H.
  elimtype False; apply n; symmetry; assumption.
  assumption.
Qed.

(* Apply a field map to a Field_in *)
Fixpoint apply_fmap s t (m : FMap t s) (f : Field_in s) : Field_in t :=
  exist _ (apply_fmap_field s t m (proj1_sig f))
        (apply_fmap_proof s t m (proj1_sig f) (proj2_sig f)).

(* The identity field map *)
Fixpoint fmap_id s : FMap s s :=
  match s with
    | 

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


(*** Models ***)

(* Helper for elements of a model at an arbitrary type *)
Definition Any : Type := { T : Type & T }.
Definition mkAny (T:Type) (t:T) : Any := existT (fun T => T) T t.
Definition anyType (any:Any) : Type := projT1 any.
Definition anyObj (any:Any) : anyType any := projT2 any.

(* A model is any list of fields and corresponding ops *)
Definition Model : Type := list (Field * Any).

(* Whether f has type T in model *)
(* FIXME: use or remove *)
Fixpoint has_type_in_model f T (model:Model) : Prop :=
  match model with
    | [] => False
    | (f', elem) :: model' =>
      (f = f' -> anyType elem = T) /\
      (f <> f' -> has_type_in_model f T model')
  end.

(* Project field f from model *)
(* FIXME: use or remove *)
Fixpoint model_proj f T (model:Model) : has_type_in_model f T model -> T :=
  match model return has_type_in_model f T model -> T with
    | [] => fun htim => match htim with end
    | (f', elem) :: model' =>
      fun htim =>
        match Field_dec f f' with
          | left e => rew (match htim with conj f _ => f e end) in (projT2 elem)
          | right neq => model_proj f T model'
                                    (match htim with conj _ f => f neq end)
        end
  end.

(* Try to project field f from model *)
Fixpoint model_proj_opt f (model:Model) : option Any :=
  match model with
    | [] => None
    | (f', elem) :: model' =>
      if Field_dec f f' then Some elem else
        model_proj_opt f model'
  end.

(* Build a model with a subset of the fields in flds by mapping each f in flds
using m to a value, if any, in model *)
Fixpoint unmap_model (m : FMap) flds (model:Model) : Model :=
  match flds with
    | [] => []
    | f :: flds' =>
      match model_proj_opt (apply_fmap m f) model with
        | Some elem => (f, elem) :: unmap_model m flds' model
        | None => unmap_model m flds' model
      end
  end.

(* FIXME: use or remove *)
Lemma unmap_model_not_in m flds model f :
  ~In f flds -> model_proj_opt f (unmap_model m flds model) = None.
  induction flds; intros.
  reflexivity.
  unfold unmap_model; fold unmap_model.
  destruct (model_proj_opt (apply_fmap m a) model).
  unfold model_proj_opt; fold model_proj_opt.
  destruct (Field_dec f a).
  elimtype False; apply H; left; symmetry; assumption.
  apply IHflds. intro; apply H; right; assumption.
  apply IHflds. intro; apply H; right; assumption.
Qed.

Lemma unmap_model_yields_none m flds model f :
  model_proj_opt (apply_fmap m f) model = None ->
  model_proj_opt f (unmap_model m flds model) = None.

Lemma unmap_model_preserves_proj m flds model f :
  In f flds -> model_proj_opt f (unmap_model m flds model)
               = model_proj_opt (apply_fmap m f) model.
  induction flds; intros.
  elimtype False; assumption.
  unfold unmap_model; fold unmap_model.
  case_eq (model_proj_opt (apply_fmap m a) model); intros.
  unfold model_proj_opt; fold model_proj_opt.
  destruct (Field_dec f a).
  rewrite e; symmetry; assumption.
  apply IHflds.
  destruct H; [ elimtype False; apply n; symmetry | ]; assumption.
  destruct H.
  

  apply IHflds.
  destruct H.
  rewrite H; rewrite H in H0; rewrite H0; unfold model_proj_opt;
    destruct (Field_dec_eq f) as [ e1 e2 ]; rewrite e2;
    reflexivity.
  
  unfold model_proj_opt; fold model_proj_opt.


(*** Specs ***)

Inductive Spec : flist -> Type :=
(* The base case contains the names and types of the axioms *)
| Spec_Axioms (axioms : list (Field * Prop)) : Spec fnil
(* Declared op: the rest of the spec can refer to the op *)
| Spec_DeclOp f flds not_in (T : Type) (rest : T -> Spec flds)
  : Spec (fcons f flds not_in)
(* Defined op: gives an element of the type *)
| Spec_DefOp f flds not_in (T : Type) (t : T) (rest : Spec flds)
  : Spec (fcons f flds not_in)
.

(* Conjoin all the axioms in an axiom list *)
Fixpoint conjoin_axioms (axioms : list (Field * Prop)) : Prop :=
  fold_left (fun P1 f_P2 => and P1 (snd f_P2)) axioms True.

(* Whether a model satisfies a spec *)
Fixpoint satisfies_spec flds spec model : Prop :=
  match spec in Spec flds with
    | Spec_Axioms axioms => conjoin_axioms axioms
    | Spec_DeclOp f flds' not_in T rest =>
      (match model_proj_opt f model with
         | Some elem =>
           exists (e: anyType elem = T),
             satisfies_spec flds' (rest (rew e in (projT2 elem))) model
         | None => False
       end)
    | Spec_DefOp f flds' not_in T t rest =>
      (match model_proj_opt f model with
         | Some elem => elem = mkAny T t /\ satisfies_spec flds' rest model
         | None => False
       end)
  end.


(*** Morphisms ***)

Definition IsMorphism (m:FMap) flds_s source flds_t target : Prop :=
  forall model,
    satisfies_spec flds_t target model ->
    satisfies_spec flds_s source (unmap_model m (proj1_sig flds_s) model).

Lemma is_morphism_id flds spec : IsMorphism fmap_id flds spec flds spec.
  intro model; induction spec; unfold satisfies_spec; fold satisfies_spec.
  intros; assumption.
  intros. destruct (model_proj_opt f model).
