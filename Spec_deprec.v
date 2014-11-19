
(*** Specs represented as dependent records ***)

Require Import List.
Import ListNotations.
Require Import String.

Add LoadPath "." as Specware.
Require Import Specware.Util.


(* Define the type of fields in one place, so we can change it later *)

Definition Field : Set := string.
Definition Field_dec : forall (f1 f2 : Field), {f1=f2} + {f1<>f2} := string_dec.


(*** Dependent record types ***)

(* Dependent record types, indexed by their fields *)
Inductive RecType : forall {flds : list Field}, Type :=
| RecType_Nil : RecType (flds:=nil)
| RecType_Cons f {flds} A :
    (A -> RecType (flds:=flds)) -> RecType (flds:= f :: flds)
| RecType_ConsAxiom f {flds} (P : Prop) :
    (P -> RecType (flds:=flds)) -> RecType (flds:= f :: flds)
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

(* Model inclusion: when all models of spec1 are models of spec2 *)
Definition Model_incl spec1 spec2 : Prop :=
  forall m, IsModelOf m spec1 -> IsModelOf m spec2.

(* Predicate for when a RecType contains a top-level field,type pair *)
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

(* A super-spec is intuitively a spec with more fields and/or axioms *)
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

