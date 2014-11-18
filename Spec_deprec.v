
(*** Specs represented as dependent records ***)

Require Import List.
Import ListNotations.
Require Import String.

Add LoadPath "." as Specware.
Require Import Specware.Util.


(* Define the type of fields in one place, so we can change it later *)

Definition Field : Set := string.
Definition Field_dec : forall (f1 f2 : Field), {f1=f2} + {f1<>f2} := string_dec.


(* Dependent record types, indexed by their fields *)
Inductive RecType : forall {flds : list Field}, Type :=
| RecType_Nil : RecType (flds:=nil)
| RecType_Cons f A {flds} :
    (A -> RecType (flds:=flds)) -> RecType (flds:= f :: flds)
.

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

