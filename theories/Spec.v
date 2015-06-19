
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
    | Spec_DeclOp _ flds' _ T rest =>
      { t : T & spec_model flds' (rest t)}
    | Spec_DefOp _ flds' _ _ _ rest => spec_model flds' rest
  end.

(* Whether field f has type T in a model *)
Fixpoint has_type_in_model f T flds spec : spec_model flds spec -> Prop :=
  match spec in Spec flds return spec_model flds spec -> Prop with
    | Spec_Axioms _ => fun model => False
    | Spec_DeclOp f' flds' not_in T' rest =>
      fun model =>
        (f = f' -> T' = T) /\
        (f <> f' ->
         has_type_in_model f T flds' (rest (projT1 model)) (projT2 model))
    | Spec_DefOp f' flds' not_in T' t' rest =>
      fun model =>
        (f = f' -> T' = T) /\
        (f <> f' -> has_type_in_model f T flds' rest model)
  end.

Lemma has_type_in_model_in_flds f T flds spec model :
  has_type_in_model f T flds spec model -> in_fl f flds.
  revert model; induction spec; intros.
  elimtype False; apply H.
  destruct (Field_dec f f0).
  rewrite e; apply in_fl_eq.
  right. apply (H (projT1 model) (projT2 model)).
  destruct H0. apply H1. assumption.
  destruct (Field_dec f f0).
  rewrite e; apply in_fl_eq.
  right; apply (IHspec model). destruct H. apply H0. assumption.
Qed.

Lemma has_type_in_model_eq_decl f T flds not_in rest model :
  has_type_in_model f T _ (Spec_DeclOp f flds not_in T rest) model.
  split; intros; [ | elimtype False; apply H ]; reflexivity.
Qed.

Lemma has_type_in_model_eq_def f T flds not_in t rest model :
  has_type_in_model f T _ (Spec_DefOp f flds not_in T t rest) model.
  split; intros; [ | elimtype False; apply H ]; reflexivity.
Qed.

Lemma has_type_in_model_cons_decl f T f' flds' not_in T' t' rest model
: f <> f' -> has_type_in_model f T flds' (rest t') model ->
  has_type_in_model f T _ (Spec_DeclOp f' flds' not_in T' rest) (existT _ t' model).
  split; [ intro H1; elimtype False; apply (H H1) | ].
  intros; assumption.
Qed.

Lemma has_type_in_model_cons_def f T f' flds' not_in T' t' rest model
: f <> f' -> has_type_in_model f T flds' rest model ->
  has_type_in_model f T _ (Spec_DefOp f' flds' not_in T' t' rest) model.
  split; [ intro H1; elimtype False; apply (H H1) | ].
  intros; assumption.
Qed.


(* Project a field out of a model of a spec *)
Fixpoint model_proj f T flds spec
: forall model, has_type_in_model f T flds spec model -> T :=
  match spec in Spec flds
        return forall model, has_type_in_model f T flds spec model -> T with
    | Spec_Axioms _ => fun model htim => (match htim with end)
    | Spec_DeclOp f' flds' not_in T' rest =>
      fun model htim =>
        match Field_dec f f' with
          | left e => eq_rect T' id (projT1 model) T (proj1 htim e)
          | right neq =>
            model_proj f T flds' (rest (projT1 model)) (projT2 model)
                       ((match htim with conj _ f => f end) neq)
        end
    | Spec_DefOp f' flds' not_in T' t rest =>
      fun model htim =>
        match Field_dec f f' with
          | left e => eq_rect T' id t T (proj1 htim e)
          | right neq => model_proj f T flds' rest model
                                    ((match htim with conj _ f => f end) neq)
        end
  end.

(*
Fixpoint model_proj f flds spec : in_fl f flds -> spec_model flds spec -> Any :=
  match spec in Spec flds
        return in_fl f flds -> spec_model flds spec -> Any with
    | Spec_Axioms _ => fun i _ => (match i with end)
    | Spec_DeclOp f' flds' not_in T rest =>
      fun i model =>
        match in_fl_inv f f' flds' not_in i with
          | left _ => mkAny T (projT1 model)
          | right i' => model_proj f flds' (rest (projT1 model)) i' (projT2 model)
        end
    | Spec_DefOp f' flds' not_in T t rest =>
      fun i model =>
        match in_fl_inv f f' flds' not_in i with
          | left _ => mkAny T t
          | right i' => model_proj f flds' rest i' model
        end
  end.
*)

(*** Model Substitution ***)

(* This is true iff a model of source can be built from a given model of target
by using field map m to map each field of source to one of target. *)
Fixpoint CanSubstModel (m : FMap) flds_s (source : Spec flds_s) flds_t
         (target : Spec flds_t) (model : spec_model _ target) : Prop :=
  match source in Spec flds_s with
    | Spec_Axioms axioms => conjoin_axioms axioms
    | Spec_DeclOp f flds_s' not_in T rest =>
      exists (htim : has_type_in_model (apply_fmap m f) T flds_t target model),
        CanSubstModel m flds_s' (rest (model_proj _ _ _ _ model htim)) flds_t target model
    | Spec_DefOp f flds_s' not_in T t rest =>
      exists (htim : has_type_in_model (apply_fmap m f) T flds_t target model),
        model_proj _ _ _ _ model htim = t /\
        CanSubstModel m flds_s' rest flds_t target model
  end.

(*
Inductive CanSubstModel (m : FMap) flds_t target (model : spec_model flds_t target) : 
  forall flds_s, Spec flds_s -> Prop :=
| CanSubst_Axioms axioms (pf : conjoin_axioms axioms)
  : CanSubstModel m flds_t target model fnil (Spec_Axioms axioms)
| CanSubst_DeclOp f flds_s not_in T rest t i
                  (e : model_proj (apply_fmap m f) _ _ i model = mkAny T t)
                  (rec : CanSubstModel m flds_t target model flds_s (rest t))
  : CanSubstModel m flds_t target model _
                  (Spec_DeclOp f flds_s not_in T rest)
| CanSubst_DefOp f flds_s not_in T rest t i
                  (e : model_proj (apply_fmap m f) _ _ i model = mkAny T t)
                  (rec : CanSubstModel m flds_t target model flds_s rest)
  : CanSubstModel m flds_t target model _
                  (Spec_DefOp f flds_s not_in T t rest)
.
*)

Lemma CanSubstModel_cons_decl m f flds_t not_in T t target model flds_s source
: CanSubstModel m flds_s source flds_t (target t) model ->
  CanSubstModel m flds_s source _ (Spec_DeclOp f flds_t not_in T target) (existT _ t model).
  induction source; unfold CanSubstModel; fold CanSubstModel; intro csm.
  assumption.
  destruct csm as [htim csm].
  assert (apply_fmap m f0 <> f) as neq.
    intro; apply not_in; rewrite <- H0;
      apply (has_type_in_model_in_flds _ _ _ _ _ htim).
  assert (apply_fmap m f0 = f -> T = T0); [ intros; contradiction | ].
  exists (conj H0 (fun _ => htim)).
  unfold model_proj; fold model_proj.
  destruct (Field_dec_neq _ _ neq); rewrite e. apply H. assumption.
  destruct csm as [htim conj]; destruct conj as [proj_eq csm].
  assert (apply_fmap m f0 <> f) as neq.
    intro; apply not_in; rewrite <- H;
      apply (has_type_in_model_in_flds _ _ _ _ _ htim).
  assert (apply_fmap m f0 = f -> T = T0); [ intros; contradiction | ].
  exists (conj H (fun _ => htim)).
  unfold model_proj; fold model_proj.
  destruct (Field_dec_neq _ _ neq); rewrite e. split.
  assumption.
  apply IHsource. assumption.
Qed.

Lemma CanSubstModel_cons_def m f flds_t not_in T t target model flds_s source
: CanSubstModel m flds_s source flds_t target model ->
  CanSubstModel m flds_s source _ (Spec_DefOp f flds_t not_in T t target) model.
  induction source; unfold CanSubstModel; fold CanSubstModel; intro csm.
  assumption.
  admit.
  admit.
Qed.


(* CanSubstModel is reflexive *)
Lemma CanSubstModel_refl flds spec model : CanSubstModel fmap_id flds spec flds spec model.
  revert model; induction spec;
    unfold CanSubstModel; fold CanSubstModel; unfold model_proj; fold model_proj; intros.
  assumption.
  rewrite fmap_id_ok. exists (in_fl_eq _ _ _). exists (projT1 model).
  unfold in_fl_inv. destruct (Field_dec_eq f) as [f_eq fdec_eq]; rewrite fdec_eq.
  split; [ reflexivity | ].
  destruct model. apply CanSubstModel_cons_decl. apply H.
  rewrite fmap_id_ok. exists (in_fl_eq _ _ _).
  unfold in_fl_inv. destruct (Field_dec_eq f) as [f_eq fdec_eq]; rewrite fdec_eq.
  split; [ reflexivity | ].
  apply CanSubstModel_cons_def. apply IHspec.
Qed.


(* Perform model substitution. This intuitively applies the map m backwards,
building a model of source from a model of target by applying m to each field in
source to get the field name for the value to use in the model of target. *)
Fixpoint subst_model m flds_s source flds_t target model :
  CanSubstModel m flds_s source flds_t target model -> spec_model flds_s source :=
  match source in Spec flds_s
        return CanSubstModel m flds_s source flds_t target model ->
               spec_model flds_s source with
    | Spec_Axioms axioms =>
      fun pf => pf
    | Spec_DeclOp f flds_s' not_in T rest =>
      fun can_subst =>
        existT (fun t => spec_model _ (rest t))
               (model_proj (apply_fmap m f) flds_t target model (proj1_sig can_subst))
               (subst_model m _ target model (proj2_sig can_subst))
    | Spec_DefOp f flds_s' not_in T t rest =>
      fun can_subst =>
        (subst_model m _ target model
                     (proj2 (proj2_sig can_subst)))
  end.




(*** FIXME: Old Stuff Below ***)


(* Whether field f has type T in a given model of spec *)
Fixpoint field_has_type f T spec : spec_model spec -> Prop :=
  match spec return spec_model spec -> Prop with
    | Spec_Axioms _ => fun model => False
    | Spec_DeclOp f' T' rest =>
      fun model =>
        if Field_dec f f' then T' = T else
          field_has_type f T (rest (projT1 model)) (projT2 model)
    | Spec_DefOp f' T' t rest =>
      fun model =>
        if Field_dec f f' then T' = T else
          field_has_type f T rest model
  end.

(* Invert field_has_type for Spec_DeclOp *)
Definition field_has_type_inv_decl f T f' T' rest :
  forall model,
    field_has_type f T (Spec_DeclOp f' T' rest) model ->
    {T' = T} + {field_has_type f T (rest (projT1 model)) (projT2 model)}.
  unfold field_has_type; fold field_has_type; unfold spec_model; fold spec_model.
  destruct (Field_dec f f'); intros.
  left; assumption.
  right; assumption.
Defined.

(* Invert field_has_type for Spec_DefOp *)
Definition field_has_type_inv_def f T f' T' t' rest :
  forall model,
    field_has_type f T (Spec_DefOp f' T' t' rest) model ->
    {T' = T} + {field_has_type f T rest model}.
  unfold field_has_type; fold field_has_type; unfold spec_model; fold spec_model.
  destruct (Field_dec f f'); intros.
  left; assumption.
  right; assumption.
Defined.


(* Project a named field out of a model of a spec *)
(*
Definition model_proj f T spec :
  forall (model:spec_model spec), field_has_type f T spec model -> T.
  induction spec; unfold field_has_type; fold field_has_type;
    unfold spec_model; fold spec_model.
  intros; elimtype False; assumption.
  destruct (Field_dec f f0).
    intros; rewrite <- H; apply (projT1 model).
    intros; apply (X (projT1 model) (projT2 model)); assumption.
  destruct (Field_dec f f0).
    intros; rewrite <- H; apply t.
    intros; apply (IHspec model); assumption.
Defined.
*)

Fixpoint model_proj f T spec :
  forall (model:spec_model spec), field_has_type f T spec model -> T :=
  match spec return forall (model:spec_model spec),
                      field_has_type f T spec model -> T with
    | Spec_Axioms _ =>
      fun model has_type => (match has_type with end)
    | Spec_DeclOp f' T' rest =>
      fun model has_type =>
        (match field_has_type_inv_decl f T f' T' rest model has_type with
           | left e => eq_rect T' id (projT1 model) T e
           | right has_type' =>
             model_proj f T (rest (projT1 model)) (projT2 model) has_type'
         end)
    | Spec_DefOp f' T' t' rest =>
      fun model has_type =>
        (match field_has_type_inv_def f T f' T' t' rest model has_type with
           | left e => eq_rect T' id t' T e
           | right has_type' =>
             model_proj f T rest model has_type'
         end)
  end.


(*** Model Substitution ***)

(* This is true iff a model of source can be built from a given model of target
by using field map m to map each field of source to one of target. *)
Fixpoint CanSubstModel (m : FMap) (source target : Spec)
         (model : spec_model target) : Prop :=
  match source with
    | Spec_Axioms axioms => conjoin_axioms axioms
    | Spec_DeclOp f T rest =>
      { has_type:field_has_type (apply_fmap m f) T target model |
        CanSubstModel m (rest (model_proj (apply_fmap m f) T target model has_type))
                      target model }
    | Spec_DefOp f T t rest =>
      { has_type:field_has_type (apply_fmap m f) T target model |
        (model_proj (apply_fmap m f) T target model has_type) = t /\
        CanSubstModel m rest target model }
  end.

(* Perform model substitution. This intuitively applies the map m backwards,
building a model of source from a model of target by applying m to each field in
source to get the field name for the value to use in the model of target. *)
Fixpoint subst_model m source target model :
  CanSubstModel m source target model -> spec_model source :=
  match source return CanSubstModel m source target model -> spec_model source with
    | Spec_Axioms axioms =>
      fun pf => pf
    | Spec_DeclOp f T rest =>
      fun can_subst =>
        existT (fun t => spec_model (rest t))
               (model_proj (apply_fmap m f) T target model (proj1_sig can_subst))
               (subst_model m _ target model (proj2_sig can_subst))
    | Spec_DefOp f T t rest =>
      fun can_subst =>
        (subst_model m _ target model
                     (proj2 (proj2_sig can_subst)))
  end.

(* CanSubstModel is reflexive *)
Lemma CanSubstModel_refl spec model : CanSubstModel fmap_id spec spec model.
  revert model; induction spec; unfold CanSubstModel; unfold spec_model;
    fold spec_model; fold CanSubstModel.
  intros; assumption.
  rewrite fmap_id_ok; intro model; destruct model as [t model].
  assert (field_has_type f T (Spec_DeclOp f T rest) (existT _ t model)) as has_type.
  unfold field_has_type; fold field_has_type;
    destruct (Field_dec_eq f) as [eq_f_f eq_field_dec]; rewrite eq_field_dec; reflexivity.
  exists has_type. unfold CanSubstModel; fold CanSubstModel.

  assert {e:Field_dec f f}

  unfold model_proj; unfold field_has_type_inv_decl; unfold projT1; unfold projT2;
fold (model_proj f T);
  destruct (Field_dec f f).
  Focus 2. fold (model_proj f T (Spec_Decl)).

exists (eq_refl T).


(*** Morphisms ***)

(* Field map m is a morphism from source to target iff it can be used to
substitute into any model of target to get a model of source *)
Definition IsMorphism (m : FMap) (source target : Spec) : Prop :=
  forall (model:spec_model target), CanSubstModel m source target model.




(*** FIXME: old stuff below ***)

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

(* NOTE: this is in Type because we need to compute the model elements *)
Fixpoint IsModel (model:Model) (s:Spec) : Prop :=
  match s with
    | Spec_Axioms axioms => conjoin_axioms axioms
    | Spec_DeclOp f T rest =>
      exists t, model_proj f model = Some (mkAny T t) /\ IsModel model (rest t)
    | Spec_DefOp f T t rest =>
      model_proj f model = Some (mkAny T t) /\ IsModel model rest
  end.


(*** Morphisms ***)

Fixpoint unmap_model (m : FMap) (model:Model) : Model := FIXME HERE

Fixpoint IsMappedModel (m : FMap) (model:Model) (s:Spec) : Prop :=
  match s with
    | Spec_Axioms axioms => conjoin_axioms axioms
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
      conjoin_axioms axioms
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
      conjoin_axioms axioms
    | Spec_DeclOp f T rest =>
      

Fixpoint IsMorphism (m : Field -> Field) (source target : Spec) : Prop :=
  match source with
    | Spec_Axioms axioms =>
      conjoin_axioms axioms
    | Spec_DeclOp f T rest =>
