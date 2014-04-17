
(*** A language for writing specs ***)

Require Import String.
Require Import List.
Import ListNotations.

(* Require Export Coq.Logic.Eqdep. *)

Add LoadPath "." as Specware.
Require Import Specware.Util.
Require Import Specware.Spec_sh.


(*** MetaSlang terms and types ***)

(* Name some type universes, to keep track of where things go *)
Definition Type1 := Type.
Definition Type0 : Type1 := Type.

Inductive MSType `{FieldType} : Type1 :=
| MS_Arrow (T1 T2 : MSType) : MSType
| MS_RecordType (fields : list F) (elems : MSTypes) : MSType
| MS_CoProduct (fields : list F) (elems : MSTypes) : MSType
(* | MS_Quotient (baseT : MSType) (eqOp : MSTerm) : MSType *)
| MS_Subtype (baseT : MSType) (pred : MSTerm) : MSType
| MS_BaseType (n : F) (args : MSTypes)
| MS_TyVar (X : F)
| MS_EmbedType (A : Type0) : MSType
with MSTypes `{FieldType} : Type1 :=
| MS_Types_Nil : MSTypes
| MS_Types_Cons : MSType -> MSTypes -> MSTypes
with MSTerm `{FieldType} : Type1 :=
| MS_Apply (M1 M2 : MSTerm) : MSTerm
| MS_Record (fields : list F) (elems : MSTerms) : MSTerm
| MS_Let (x : F) (M_right M_body : MSTerm) : MSTerm
(* | LetRec       List (AVar b     * ATerm b) * ATerm b   * b *)
| MS_Var (x : F + F) (* can be a var or a Spec field *)
| MS_Builtin (op : F) : MSTerm
| MS_Lambda (x : F) (T : MSType) (M : MSTerm) : MSTerm
| MS_IfThenElse (T1 T2 T3 : MSTerm) : MSTerm
(* | Seq          List (ATerm b)                          * b *)
(*  | TypedTerm    ATerm b * AType b                       * b *)
(*  | Transform    List(ATransformExpr b)                  * b  % For specifying refinement by script *)
| MS_TyLambda (X : F) (M : MSTerm)
| MS_EmbedObj (A : Type0) (a : A) : MSTerm
with MSTerms `{FieldType} : Type1 :=
| MS_Terms_Nil : MSTerms
| MS_Terms_Cons : MSTerm -> MSTerms -> MSTerms
.

Inductive MSPolyType `{FieldType} : Type1 :=
| MSPolyType_Base (T : MSType)
| MSPolyType_Forall (X : F) (body : MSPolyType)
.


(*** Typing contexts ***)

Definition ctxElem `{FieldType} : Type1 := 


(*** Typing and kinding rules ***)

Inductive 


(*** Interpreting terms and types ***)

Definition 

Fixpoint interpType `{FieldType} (list )
