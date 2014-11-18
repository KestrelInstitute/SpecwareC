
(*** Specs represented as dependent records ***)

Require Import List.
Import ListNotations.
Require Import String.

Add LoadPath "." as Specware.
Require Import Specware.Util.


(* Define the type of fields in one place, so we can change it later *)

Definition Field : Set := string.
Definition Field_dec : forall (f1 f2 : Field), {f1=f2} + {f1<>f2} := string_dec.

Definition FieldList : Set := { flds : list Field | NoDup flds }.

Definition map_NoDup (f : Field -> Field) (flds : FieldList) : FieldList :=
  FIXME HERE.



(* Dependent record types, indexed by their fields *)
Inductive RecType : forall {flds : FieldList}, Type :=
| RecType_Nil : RecType (flds:=nil)
| RecType_Cons f A {flds} :
    (A -> RecType (flds:=flds)) -> RecType (flds:= f :: flds)
.

Fixpoint map_RecType (f : Field -> Field) {flds} (rectp : @RecType flds) :
  @RecType (map_NoDup f flds) :=
  FIXME HERE.

(* Elements of dependent record types (FIXME: unnecessary?) *)
(*
Inductive RecElem : forall {flds : list Field}, @RecType flds -> Type :=
| RecElem_Nil : RecElem RecType_Nil
| RecElem_Cons f A (a:A) {flds} (rectp: A -> @RecType flds)
               (rest: RecElem (rectp a)) :
    RecElem (RecType_Cons f A rectp)
.
*)

(* Dependent records, independent of record type *)
Inductive RecElem : forall {flds : list Field}, Type :=
| RecElem_Nil : @RecElem nil
| RecElem_Cons f A (a:A) {flds} (rest: @RecElem flds) :
    @RecElem (f :: flds)
.

(* Helper lemma for lists *)
Lemma In_inv_neq A (a b : A) l :
  In a (b :: l) -> b <> a -> In a l.
  intros in_ab neq; destruct (in_inv in_ab);
  [ elimtype False; apply (neq H) | assumption ].
Qed.

(* Projecting a field in a RecElem *)
Fixpoint RecElem_proj {flds} (elem: @RecElem flds) :
  {f:Field | In f flds} -> { A : Type & A } :=
  match elem in @RecElem flds return {f:Field | In f flds} -> { A : Type & A } with
    | RecElem_Nil =>
      (fun f => match in_nil (projT2 f) with end)
    | RecElem_Cons f' A a _ elem' =>
      (fun f =>
         match Field_dec f' (projT1 f) with
           | left _ => existT id A a
           | right neq_pf =>
             RecElem_proj elem' (existT _ (projT1 f)
                                        (In_inv_neq _ _ _ _ (projT2 f) neq_pf))
         end)
  end.


FIXME HERE:
* define the restriction of a RecElem to a particular FieldList
* loosen the IsElemOf to allow re-ordering and subsetting of fields
* define morphisms s1 >=> s2 as:
  forall models m of s2, applying a mapping to RecType s1 yields another s1'
  such that the model m IsElemOf s1'


(* When a RecElem is an element of a RecType *)
Inductive IsElemOf :
  forall {flds : list Field}, @RecType flds -> @RecElem flds -> Prop :=
| IsElemOf_Nil : IsElemOf RecType_Nil RecElem_Nil
| IsElemOf_Cons f A a {flds} (rest_tp: A -> @RecType flds)
                (rest_elem: @RecElem flds) :
    IsElemOf (rest_tp a) rest_elem ->
    IsElemOf (RecType_Cons f A rest_tp) (RecElem_Cons f A a rest_elem)
.

(* Bundling together RecElem with IsElemOf *)
Definition RecElemOf {flds} (rectp: @RecType flds) :=
  { elem: @RecElem flds | IsElemOf rectp elem }.



(* A Spec is a RecType with an arbitrary list of fields *)
Record Spec :=
  {
    spec_fields : list Field;
    spec_fields_nodups : NoDup spec_fields;
    spec_recType : @RecType spec_fields
  }.

