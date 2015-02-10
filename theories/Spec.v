
(*** Specs represented as dependent records ***)

Require Import List.
Import ListNotations.
Require Import String.

Add LoadPath "." as Specware.
Require Import Specware.Util.


(* Define the type of fields in one place, so we can change it later *)

Definition Field : Set := string.
Definition Field_dec : forall (f1 f2 : Field), {f1=f2} + {f1<>f2} := string_dec.


(*** Signatures ***)

(* A signature is essentially a structuring device for describing a
   dependent record type. The type Sig S describes a signature whose
   models are the elements of type S. *)
Inductive Sig : Type -> Type :=
| Sig_Empty : Sig unit
| Sig_AddOp S (s: Sig S) (f : Field) (A : S -> Type) : Sig { s:S & A s }
| Sig_AddAxiom S (s: Sig S) (f : Field) (P : S -> Prop) : Sig { s:S | P s }
| Sig_Import S1 (s1: Sig S1) S2 (s2: Sig S2) : Sig (S1 * S2)
.

(* The op fields of a signature *)
Fixpoint op_fields S (s: Sig S) : list Field :=
  match s in Sig S with
    | Sig_Empty => []
    | Sig_AddOp S' s' f _ => f :: op_fields S' s'
    | Sig_AddAxiom S' s' _ _ => op_fields S' s'
    | Sig_Import S1 s1 S2 s2 => op_fields S1 s1 ++ op_fields S2 s2
  end.

(* The data (non-proof) fields of a signature *)
Fixpoint axiom_fields S (s: Sig S) : list Field :=
  match s in Sig S with
    | Sig_Empty => []
    | Sig_AddOp S' s' _ _ => axiom_fields S' s'
    | Sig_AddAxiom S' s' f _ => f :: axiom_fields S' s'
    | Sig_Import S1 s1 S2 s2 => axiom_fields S1 s1 ++ axiom_fields S2 s2
  end.


(*** Model projections ***)

Definition Any := { A : Type & A}.
Definition mkAny A a : Any := existT id A a.

Program Fixpoint model_proj S (s:Sig S) : { f: Field | In f (op_fields S s) } -> S -> Any :=
  match s in Sig S return { f: Field | In f (op_fields S s) } -> S -> Any with
    | Sig_Empty =>
      fun f _ => match proj2_sig f with end
    | Sig_AddOp S' s' f' A =>
      fun f M =>
        match Field_dec f f' with
          | left _ => mkAny _ (projT2 M)
          | right neq =>
            model_proj S' s' f (projT1 M)
        end
    | Sig_AddAxiom S' s' _ _ =>
      fun f M => model_proj S' s' f (proj1_sig M)
    | Sig_Import S1 s1 S2 s2 =>
      fun f M =>
        match in_dec Field_dec f (op_fields S1 s1) with
          | left in1 => model_proj S1 s1 f (fst M)
          | right not_in1 => model_proj S2 s2 f (snd M)
        end
  end.
Obligation 1.
destruct H; [ elimtype False; apply neq; symmetry | ]; assumption.
Defined.
Obligation 3.
destruct (in_app_or _ _ _ H); [ elimtype False; apply not_in1 | ]; assumption.
Defined.


(*** Morphisms ***)

Definition IsMorphism (g: Field -> Field) S1 (s1:Sig S1) S2 (s2:Sig S2) : Prop :=
  exists embed (embed_fields :
                  forall f, In f (op_fields S1 s1) ->
                            In (g f) (op_fields S2 s2)),
    forall f i M2, model_proj S1 s1 (exist _ f i) (embed M2) =
                   model_proj S2 s2 (exist _ (g f) (embed_fields f i)) M2.
