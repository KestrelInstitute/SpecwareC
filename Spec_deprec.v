
(*** Specs represented as dependent records ***)

Require Import List.
Import ListNotations.
Require Import String.

Add LoadPath "." as Specware.
Require Import Specware.Util.


(* Define the type of fields in one place, so we can change it later *)

Definition Field : Set := string.
Definition Field_dec : forall (f1 f2 : Field), {f1=f2} + {f1<>f2} := string_dec.

(* Type-level versions of bool and unit (needed below) *)
Inductive boolT : Type := | trueT : boolT | falseT : boolT.
Inductive unitT : Type := | ttT : unitT.

Definition boolTT : Type := boolT.
Definition unitTT : Type := unitT.

Lemma neq_trueT_falseT : trueT = falseT -> False.
  discriminate.
Qed.

(* The types bool and unit (in universe Type) are unequal *)
Lemma bool_neq_unit : boolTT = unitTT -> False.
  intro e; apply neq_trueT_falseT.
  transitivity (eq_rect unitTT id (eq_rect boolTT id trueT unitTT e) boolTT (eq_sym e)).
  unfold eq_rect; destruct e; unfold eq_sym; reflexivity.
  transitivity (eq_rect unitTT id (eq_rect boolTT id falseT unitTT e) boolTT (eq_sym e)).
  destruct (eq_rect boolTT id trueT unitTT e); destruct (eq_rect boolTT id falseT unitTT e); reflexivity.
  unfold eq_rect; destruct e; unfold eq_sym; reflexivity.
Qed.


(*** Dependent record types ***)

(* Dependent record types, indexed by their fields *)
Inductive RecType : forall {flds : list Field}, Type :=
| RecType_Nil : RecType (flds:=nil)
| RecType_Cons f {flds} A (rectp: A -> RecType (flds:=flds)) :
    RecType (flds:= f :: flds)
| RecType_ConsAxiom f {flds} (P : Prop) (rectp: P -> RecType (flds:=flds)) :
    RecType (flds:= f :: flds)
.

(* Map a function over the fields of a RecType *)
Fixpoint map_RecType (g : Field -> Field) {flds} (rectp : @RecType flds) :
  @RecType (map g flds) :=
  match rectp in @RecType flds return @RecType (map g flds) with
    | RecType_Nil =>
      RecType_Nil
    | RecType_Cons f _ A rectp' =>
      RecType_Cons (g f) A (fun a => map_RecType g (rectp' a))
    | RecType_ConsAxiom f _ P rectp' =>
      RecType_ConsAxiom (g f) P (fun pf => map_RecType g (rectp' pf))
  end.

(*** Subtypes ***)

(* README: need subtype to be predicative in order to project along it! *)
(*
Inductive subtype : Type -> Type -> Prop :=
| subtype_refl A : subtype A A
| subtype_trans A1 A2 A3 (s1 : subtype A1 A2) (s2: subtype A2 A3) : subtype A1 A3
| subtype_subsume A (P1 P2: A -> Prop) (sub: forall a, P1 a -> P2 a) :
    subtype (sig P1) (sig P2)
| subtype_restrict A (P: A -> Prop) : subtype (sig P) A
| subtype_true A (P: A -> Prop) (truth: forall a, P a) :
    subtype A (sig P)
.
*)


(*** Models, aka records, aka heterogenous lists ***)

Definition Any := { A : Type & A}.
Definition mkAny A a : Any := existT id A a.
Definition Model := list (Field * Any).

(* Project a field from a Model, returning unit if the field is not
   there; i.e., all models intuitively map unused fields to unit *)
Fixpoint Model_proj (model : Model) f : Any :=
  match model with
    | nil => existT id unit tt
    | (f', any) :: model' =>
      if Field_dec f' f then any else Model_proj model' f
  end.

(* Project just the type component from a Model *)
Definition Model_projT (model : Model) f : Type :=
  projT1 (Model_proj model f).

(* Project just the object component from a Model *)
Definition Model_projO (model : Model) f : Model_projT model f :=
  projT2 (Model_proj model f).

(* When a Model is a model of a RecType *)
Inductive IsModelOf_RT (m: Model) : forall {flds}, @RecType flds -> Prop :=
| IsModelOf_RT_Nil : IsModelOf_RT m RecType_Nil
| IsModelOf_RT_Cons f {flds}
                    (rectp : Model_projT m f -> @RecType flds)
                    (model_of : IsModelOf_RT m (rectp (Model_projO m f)))
 : IsModelOf_RT m (RecType_Cons f (Model_projT m f) rectp)
| IsModelOf_RT_ConsAxiom f {flds} (P:Prop) pf (rectp : P -> @RecType flds)
                         (model_of : IsModelOf_RT m (rectp pf))
 : IsModelOf_RT m (RecType_ConsAxiom f P rectp)
.


(*** Lowering ***)

(* Lower Prop P inside rectp, i.e., augment it to quantify over all
   types / axioms of rectp. Note that lowering P is stronger than
   (forall m, IsModelOf_RT m rectp -> P) since lowering is insensitive
   to duplicate fields *)
Fixpoint RecType_lowerP {flds} (rectp: @RecType flds) (P:Prop) : Prop :=
  match rectp with
    | RecType_Nil => P
    | RecType_Cons f' flds' A' rectp' =>
      forall a, RecType_lowerP (rectp' a) P
    | RecType_ConsAxiom f' flds' P' rectp' =>
      forall pf, RecType_lowerP (rectp' pf) P
  end.

(* Same as above, but in Type instead of Prop *)
Fixpoint RecType_lower {flds} (rectp: @RecType flds) A : Type :=
  match rectp with
    | RecType_Nil => A
    | RecType_Cons f' flds' A' rectp' =>
      forall a, RecType_lower (rectp' a) A
    | RecType_ConsAxiom f' flds' P rectp' =>
      forall pf, RecType_lower (rectp' pf) A
  end.

(*
Lemma lowerP_Cons f A {flds} (rectp: A -> @RecType flds) (P:Prop) :
  RecType_lowerP rectp P -> 
*)

Lemma lowered_in_model {flds} (rectp: @RecType flds) (P:Prop)
      (loweredP: RecType_lowerP rectp P)
      model (ismodel: IsModelOf_RT model rectp) : P.
  induction ismodel.
  apply loweredP.
  apply IHismodel; apply loweredP.
  apply IHismodel; apply loweredP.
Qed.


(*** Specs ***)

(* A Spec is a RecType with an arbitrary field list *)
Record Spec : Type :=
  {
    spec_fields : list Field;
    spec_recType : @RecType spec_fields
  }.

(* Mapping specs *)
Definition mapSpec (g : Field -> Field) (spec: Spec) : Spec :=
  {| spec_recType := map_RecType g (spec_recType spec) |}.

(* When a Model is a model of a Spec *)
Definition IsModelOf (m: Model) (spec: Spec) : Prop :=
  IsModelOf_RT m (spec_recType spec).


(*** Sub-specs and model inclusion ***)

(* Model inclusion: when all models of rectp1 are models of rectp2 *)
Definition Model_incl_RT {flds1} rectp1 {flds2} rectp2 : Prop :=
  forall m, @IsModelOf_RT m flds1 rectp1 -> @IsModelOf_RT m flds2 rectp2.

(* Model inclusion: when all models of spec1 are models of spec2 *)
Definition Model_incl spec1 spec2 : Prop :=
  forall m, IsModelOf m spec1 -> IsModelOf m spec2.

(* Predicate for when a RecType contains a top-level field,type pair *)
Fixpoint RecTypeContains (f:Field) (A:Type) {flds} (rectp: @RecType flds) : Prop :=
  match rectp with
    | RecType_Nil => False
    | RecType_Cons f' flds' A' rectp' =>
      (f = f' /\ forall a, RecType_lowerP (rectp' a) (A = A'))
      \/ (forall a, RecTypeContains f A (rectp' a))
    | RecType_ConsAxiom f' flds' P rectp' =>
      (forall pf, RecTypeContains f A (rectp' pf))
  end.
(*
Inductive RecTypeContains (f:Field) (A:Type) :
  forall {flds}, @RecType flds -> Prop :=
| RecTypeContains_Base {flds} rectp :
    RecTypeContains f A (@RecType_Cons f flds A rectp)
| RecTypeContains_Cons f' {flds} A' rectp :
    (forall a, RecTypeContains f A (rectp a)) ->
    RecTypeContains f A (@RecType_Cons f' flds A' rectp)
| RecTypeContains_ConsAxiom f' {flds} P rectp :
    (forall pf, RecTypeContains f A (rectp pf)) ->
    RecTypeContains f A (@RecType_ConsAxiom f' flds P rectp)
.
*)

(* A super-spec is intuitively a spec with more fields and/or axioms *)
Fixpoint SuperRecType {flds1} (rectp1: @RecType flds1) {flds2} (rectp2: @RecType flds2) : Prop :=
  match rectp2 with
    | RecType_Nil => True
    | RecType_Cons f flds2' A rectp2' =>
      (RecTypeContains f A rectp1) /\
      (forall a, SuperRecType rectp1 (rectp2' a))
    | RecType_ConsAxiom f flds2' P rectp2' =>
      (forall model, IsModelOf_RT model rectp1 -> P) /\
      (forall pf, SuperRecType rectp1 (rectp2' pf))
  end.
(*
Inductive SuperRecType {flds1} (rectp1: @RecType flds1) :
  forall {flds2}, @RecType flds2 -> Prop :=
| SuperRecType_Nil : SuperRecType rectp1 RecType_Nil
| SuperRecType_Cons f {flds2} A rectp2 :
    (forall a, @SuperRecType flds1 rectp1 flds2 (rectp2 a)) ->
    RecTypeContains f A rectp1 ->
    SuperRecType rectp1 (RecType_Cons f A rectp2)
| SuperRecType_ConsAxiom f {flds2} (P:Prop) rectp2 :
    (forall pf, @SuperRecType flds1 rectp1 flds2 (rectp2 pf)) ->
    (forall model, IsModelOf_RT model rectp1 -> P) ->
    SuperRecType rectp1 (RecType_ConsAxiom f P rectp2)
.
*)

Definition SuperSpec spec1 spec2 :=
  SuperRecType (spec_recType spec1) (spec_recType spec2).

(* Helper lemma for Soundness: if a Spec contains field f at type A
   then any model of that spec contains an element at f of type A *)
Lemma RecTypeContains_Model_proj model {flds} rectp
      (ismodelof: @IsModelOf_RT model flds rectp) :
  forall f A, RecTypeContains f A rectp -> Model_projT model f = A.
  induction ismodelof.
  intros f A rtc; elimtype False; apply rtc.
  intros f' A rtc; destruct rtc;
  [ destruct H as [ ef eA ]; rewrite ef; rewrite (lowered_in_model _ _ (eA _) _ ismodelof); reflexivity
  | apply IHismodelof; apply H ].
  intros; apply IHismodelof; apply H.
Qed.

(* Soundness of SuperRecType: it implies model inclusion *)
Lemma SuperRecType_Soundness {flds1} rectp1 {flds2} rectp2 :
  @SuperRecType flds1 rectp1 flds2 rectp2 -> Model_incl_RT rectp1 rectp2.
  induction rectp2.
  intros _ model _; apply IsModelOf_RT_Nil.
  intros super model ismodelof; destruct super.
  revert rectp H H1;
  rewrite <- (RecTypeContains_Model_proj _ _ ismodelof _ _ H0); intros.
  apply IsModelOf_RT_Cons.
  apply (H _ (H1 _)); assumption.
  intros super model ismodelof; destruct super.
  apply (IsModelOf_RT_ConsAxiom _ _ _ (H0 _ ismodelof)).
  apply H; [ apply H1 | assumption ].
Qed.

(* Any inhabited type A is not equal to A -> False *) Print eq_rect.
Definition exists_unequal_type (A:Type) (a:A) : A <> (A -> False) :=
  fun e => (eq_rect A id a (A -> False) e) a.

(* Helper lemma for Completeness: if all models of a Spec contain
   field f of type A then the spec contains field f of type A *)
Lemma Model_proj_RecTypeContains f {flds} A rectp :
  (forall model, @IsModelOf_RT model flds rectp -> Model_projT model f = A) ->
  RecTypeContains f A rectp.
  induction rectp.

  intro allmodels; elimtype False; apply bool_neq_unit.
  transitivity (Model_projT [(f,mkAny boolTT trueT)] f);
    [ unfold Model_projT; unfold Model_proj;
      rewrite F_dec_true; unfold mkAny; unfold projT1; reflexivity | ].
  transitivity (Model_projT [(f,mkAny unitTT ttT)] f);
    [ 
    | unfold Model_projT; unfold Model_proj;
      rewrite F_dec_true; unfold mkAny; unfold projT1; reflexivity ].
  rewrite (allmodels _ (IsModelOf_RT_Nil _));
  rewrite (allmodels _ (IsModelOf_RT_Nil _));
  reflexivity.

  intro allmodels; destruct (Field_dec f f0).
  rewrite <- e; left; split; [ reflexivity | ].
  intros a model ismodelof.

  FIXME HERE: move the quantification over models out of
  RecTypeContains and make it a global quantification at the top level
  of the definition of SuperRecType

rewrite <- (allmodels ).
Qed.

(* Completeness of SuperRecType: it is implied by model inclusion *)
Lemma SuperRecType_Completeness {flds1} rectp1 {flds2} rectp2 :
  Model_incl_RT rectp1 rectp2 -> @SuperRecType flds1 rectp1 flds2 rectp2.
  induction rectp2.
  constructor.
  intro; split.



(*** Morphisms ***)

(* A morphism is a function that maps a spec to a super-spec of another *)
Definition IsMorphism (g: Field -> Field) spec1 spec2 : Prop :=
  Model_incl spec2 (mapSpec g spec1).

(* A morphism from spec1 to spec2 is a function plus a proof that the
   function is a morphism *)
Record Morphism spec1 spec2 :=
  {
    morphism_fun : Field -> Field;
    morphism_pf : IsMorphism morphism_fun spec1 spec2
  }.

Notation "s1 >=> s2" := (Morphism s1 s2) (at level 70).


(*** Transitivity of morphisms ***)

Lemma map_Model_incl g spec1 spec2 :
  Model_incl spec1 spec2 -> Model_incl (mapSpec g spec1) (mapSpec g spec2).
  intro mincl.

