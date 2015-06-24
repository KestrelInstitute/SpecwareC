
(*** Modeling specs and morphisms as Coq terms ***)

(* This approach attempts to model field maps as morphisms in a category of
non-duplicated field lists. I got stuck on the complexity of flist_rect_H,
below... *)

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

(*** Field lists, with no duplicates ***)

Inductive flist : list Field -> Set :=
| fnil : flist []
| fcons f {l} (flist' : flist l) (not_in : ~In f l) : flist (f::l)
.

Definition in_fl f {l} (fl : flist l) : Prop := In f l.

Definition in_fl_dec f {l} fl : {@in_fl f l fl} + {~ @in_fl f l fl} :=
  In_dec Field_dec f l.

Lemma in_fl_eq f l fl pf : @in_fl f (f::l) (fcons f pf fl).
  left; reflexivity.
Qed.

Lemma flist_NoDup {l} (fl : flist l) : NoDup l.
  induction fl; constructor; assumption.
Qed.

(*
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
*)

(* A field in a field list *)
Definition Field_in {l} fl : Set := { f : Field | @in_fl f l fl }.

Definition mk_Field_in {l} fl f in_fl : @Field_in l fl := exist _ f in_fl.

(* In proofs in lists without duplicates are always equal *)
Lemma in_fl_proofs_eq (f:Field) l (nd:NoDup l) (in1 in2 : In f l) : in1 = in2.
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

(* Decidable equaltiy on Field_in *)
Definition Field_in_dec {l} fl (f1 f2 : @Field_in l fl) : {f1=f2} + {f1 <> f2}.
  destruct f1 as [f1 in1]; destruct f2 as [f2 in2]; destruct (Field_dec f1 f2).
  revert in1 in2; rewrite e; intros; left;
    f_equal; apply in_fl_proofs_eq; apply flist_NoDup; assumption.
  right. injection. assumption.
Qed.

Lemma Field_in_dec_eq {l} fl f1 pf1 f2 pf2
: f1 = f2 -> { e | @Field_in_dec l fl (exist _ f1 pf1) (exist _ f2 pf2) = left e }.
  intro e; destruct (Field_in_dec fl (exist _ f1 pf1) (exist _ f2 pf2)).
  exists e0; reflexivity.
  revert pf1 pf2 n; rewrite e; intros.
  elimtype False; apply n; f_equal;
    apply in_fl_proofs_eq; apply flist_NoDup; assumption.
Qed.

Lemma Field_in_dec_neq {l} fl f1 pf1 f2 pf2
: f1 <> f2 -> { neq | @Field_in_dec l fl (exist _ f1 pf1) (exist _ f2 pf2) = right neq }.
  intro neq; destruct (Field_in_dec fl (exist _ f1 pf1) (exist _ f2 pf2)).
  elimtype False; apply neq; injection e; intros; assumption.
  exists n; reflexivity.
Qed.


(*** The category of field maps on field lists ***)

(* The underlying type of an FMap is an association list on Fields *)
Definition FMap_alist := list (Field * Field).

(* Apply a field map to a field *)
Fixpoint apply_fmap_field (m : FMap_alist) (f : Field) : Field := 
  match m with
    | [] => f
    | (f_from, f_to) :: m' =>
      if Field_dec f f_from then f_to else apply_fmap_field m' f
  end.

(* Whether an FMap_alist maps from source s to target t *)
Definition is_fmap {sl} (s: flist sl) {tl} (t: flist tl) (alist: FMap_alist) :=
  map fst alist = sl /\
  forall f, In f sl -> In (apply_fmap_field alist f) tl.

(* The bundled type of field maps from s to t *)
Definition FMap {sl} (s : flist sl) {tl} (t : flist tl) :=
  { alist : FMap_alist | is_fmap s t alist }.

(* Apply a bundled FMap to a field in source s to get a field in target t *)
Definition apply_fmap {sl s tl t} (m : @FMap sl s tl t) (f : Field_in s) : Field_in t :=
  mk_Field_in t (apply_fmap_field (proj1_sig m) (proj1_sig f))
              (proj2 (proj2_sig m) (proj1_sig f) (proj2_sig f)).

(* Build the identity alist *)
Fixpoint fmap_id_alist l : FMap_alist :=
  match l with
    | [] => []
    | f::l' => (f,f) :: fmap_id_alist l'
  end.

(* Proof that the identity alist is an FMap *)
Lemma fmap_id_proof sl s : @is_fmap sl s sl s (fmap_id_alist sl).
  induction s; unfold fmap_id_alist; fold fmap_id_alist.
  split; [ reflexivity | intros; elimtype False; assumption ].
  destruct IHs; split.
  unfold map; fold (map fst (fmap_id_alist l)); f_equal; assumption.
  intros; unfold apply_fmap_field; fold apply_fmap_field.
  destruct (Field_dec f0 f).
  rewrite e in H1; assumption.
  right; apply H0; destruct H1.
  elimtype False; apply n; symmetry; assumption.
  assumption.
Qed.

(* Bundled identity morphism on flist s *)
Definition fmap_id {sl} s : @FMap sl s sl s :=
  exist _ (fmap_id_alist sl) (fmap_id_proof sl s).

(* Applying fmap_id is the identity *)
Lemma fmap_id_id sl s f : proj1_sig (apply_fmap (@fmap_id sl s) f) = proj1_sig (f).
  destruct f as [f in_s]; unfold apply_fmap; unfold proj1_sig;
    unfold mk_Field_in; unfold fmap_id.
  induction s.
  reflexivity.
  unfold fmap_id_alist; fold fmap_id_alist;
    unfold apply_fmap_field; fold apply_fmap_field.
  destruct (Field_dec f f0).
  symmetry; assumption.
  apply IHs. destruct in_s.
  elimtype False; apply n; symmetry; assumption.
  assumption.
Qed.

(* Compose two field map alists *)
Fixpoint fmap_compose_alist (m2 m1 : FMap_alist) : FMap_alist :=
  match m1 with
    | [] => []
    | (f_in, f_out) :: m1' =>
      (f_in, apply_fmap_field m2 f_out) :: fmap_compose_alist m2 m1'
  end.

(* Composing two field maps returns a field map *)
Lemma fmap_compose_proof l1 fl1 l2 fl2 l3 fl3 m2 m1 :
  @is_fmap l1 fl1 l2 fl2 m1 -> @is_fmap l2 fl2 l3 fl3 m2 ->
  @is_fmap l1 fl1 l3 fl3 (fmap_compose_alist m2 m1).
  revert l2 fl2 l3 fl3 m1 m2; induction fl1; intros.
  destruct m1.
  split; [ reflexivity | intros; elimtype False; assumption ].
  elimtype False; destruct H; destruct p; apply (@nil_cons _ f (map fst m1));
    symmetry; assumption.
  destruct m1.
  elimtype False; destruct H; apply (nil_cons H).
  destruct H; destruct p.
  injection H; intros.
  revert H1; unfold apply_fmap_field; fold apply_fmap_field; rewrite H3; intros.
  destruct (IHfl1 l2 fl2 l3 fl3 m1 m2).
  split.
  assumption.
  intros. assert (In f2 (f::l)); [ right; assumption | ].
  replace (apply_fmap_field m1 f2) with
    (if Field_dec f2 f then f1 else apply_fmap_field m1 f2);
    [ apply H1; assumption | ].
  destruct (Field_dec f2 f).
  elimtype False; apply not_in; rewrite e in H4; assumption.
  reflexivity.
  assumption.
  unfold fmap_compose_alist; fold fmap_compose_alist.
  split.
  unfold map; fold (@map _ Field (@fst _ Field)); f_equal; assumption.
  intros.
  unfold apply_fmap_field; fold apply_fmap_field.
  destruct (Field_dec f2 f).
  destruct H0; apply H7.
  replace f1 with (if Field_dec f0 f then f1 else apply_fmap_field m1 f0).
  apply H1; left; symmetry; assumption.
  rewrite H3. destruct (Field_dec_eq f) as [ e3 e4 ]; rewrite e4; reflexivity.
  apply H5. destruct H6.
  elimtype False; apply n; symmetry; assumption.
  assumption.
Qed.

(* Bundled composition of two morphisms *)
Definition fmap_compose {l1 fl1 l2 fl2 l3 fl3} m2 m1 : FMap fl1 fl3 :=
  exist _ (fmap_compose_alist (proj1_sig m2) (proj1_sig m1))
        (fmap_compose_proof l1 fl1 l2 fl2 l3 fl3
                            (proj1_sig m2) (proj1_sig m1)
                            (proj2_sig m1) (proj2_sig m2)).

(* Field map composition commutes with application *)
Lemma fmap_compose_composes l1 fl1 l2 fl2 l3 fl3 (m2 : FMap fl2 fl3) (m1 : FMap fl1 fl2) f :
  proj1_sig (apply_fmap (@fmap_compose l1 fl1 l2 fl2 l3 fl3 m2 m1) f)
  = proj1_sig (apply_fmap m2 (apply_fmap m1 f)).
  destruct f as [f in_s]; destruct m1 as [m1 is_map1];
  destruct m2 as [m2 is_map2]; unfold apply_fmap;
    unfold mk_Field_in; unfold fmap_compose; unfold proj1_sig.
  revert l1 fl1 is_map1 in_s. induction m1; intros.
  elimtype False.
  destruct is_map1. unfold in_fl in in_s. rewrite <- H in in_s. apply in_s.
  destruct a.
  unfold apply_fmap_field; unfold fmap_compose_alist;
    fold fmap_compose_alist; fold apply_fmap_field.
  destruct (Field_dec f f0).
  reflexivity.
  destruct fl1;
    [ elimtype False; destruct is_map1; apply (nil_cons (eq_sym H)) | ].
  destruct is_map1. injection H; intros.
  apply (IHm1 _ fl1).
  split.
  assumption.
  intros.
  replace (apply_fmap_field m1 f3) with (apply_fmap_field ((f0, f1) :: m1) f3).
  apply H0; right; assumption.
  unfold apply_fmap_field; fold apply_fmap_field.
  destruct (Field_dec_neq f3 f0).
  rewrite H2. intro. apply not_in. rewrite <- H4. assumption.
  rewrite e. reflexivity.
  destruct in_s.
  elimtype False; apply n; rewrite H2; rewrite H3; reflexivity.
  assumption.
Qed.


(*** Models ***)

(* Helper for elements of a model at an arbitrary type *)
Definition Any : Type := { T : Type & T }.
Definition mkAny (T:Type) (t:T) : Any := existT (fun T => T) T t.
Definition anyType (any:Any) : Type := projT1 any.
Definition anyObj (any:Any) : anyType any := projT2 any.

(* A model is any list of fields and corresponding ops *)
Definition Model {l} (fl : flist l) : Type :=
  fun f 

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
