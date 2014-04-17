
(*** Tactics for Refinement ***)

Require Import String.

Add LoadPath "." as Specware.
Require Import Specware.Util.
Require Export Specware.Spec_sh.

Import ListNotations.
Require Export Coq.Logic.Eqdep.


(*** Refinements and helper defs ***)

(* a Refinement of a spec is another spec and a morphism to it *)
Inductive Refinement {flds} (spec : Spec (flds:=flds)) : Type :=
| mkRefinement {flds'} (spec' : Spec (flds:=flds')) (morph : Morphism spec spec')
  : Refinement spec.

(* An existential type for a spec that hides the fields when printing *)
Inductive SomeSpec : Type :=
| mkSomeSpec {flds : list Field} (spec : Spec (flds:=flds)) : SomeSpec.

(* Extracting the destination spec of a Refinement *)
Definition refinementSpec {flds} {spec : Spec (flds:=flds)} (ref : Refinement spec) : SomeSpec :=
  match ref with
    | mkRefinement _ spec' _ => mkSomeSpec spec'
  end.

(*** The simplest refinement tactic: finish refinement (you're done) ***)

(* The identity refinement *)
Definition id_refinement {flds} spec : Refinement (flds:=flds) spec :=
  mkRefinement spec spec (mid _).

(* the tactic the ends refinement, giving the current spec being refined as the output *)
Ltac end_refine := apply id_refinement.


(*** A Refinement step that applies a morphism ***)

(* Applying a morphism to prove a refinement goal *)
Definition apply_morphism_fun {flds1} {spec1 : Spec (flds:=flds1)}
           {flds2} {spec2 : Spec (flds:=flds2)}
           (m12 : Morphism spec1 spec2) :
  Refinement spec2 ->
  Refinement spec1.
  intro ref2; destruct ref2 as [ flds3 spec3 m23 ].
  apply (mkRefinement _ spec3);
  apply (mcompose m12 m23).
Defined.

(* The above as a tactic, so we don't have to write "apply apply_morphism" *)
Ltac apply_morphism morph := apply (apply_morphism_fun morph).


(*** Refinement of sub-specs ***)

Definition IsMorphism_ConsNone f A {flds1} spec1 {flds2} spec2 m :
  (forall a, IsMorphism (flds1:=flds1) (spec1 a) (flds2:=flds2) (spec2 a) m) ->
  IsMorphism (Spec_ConsNone f A spec1) (Spec_ConsNone (applyFM m f) A spec2) m.
  intros ismorph model ism.
  destruct ism as [ a sig ]; destruct sig as [ melem ism ].
  exists a; split; [ | apply ismorph ]; assumption.
Qed.

Definition IsMorphism_ConsSome f A a {flds1} spec1 {flds2} spec2 m :
  IsMorphism (flds1:=flds1) spec1 (flds2:=flds2) spec2 m ->
  IsMorphism (Spec_ConsSome f A a spec1) (Spec_ConsSome (applyFM m f) A a spec2) m.
  intros ismorph model ism.
  destruct ism as [ melem ism ]; split; [ | apply ismorph ]; assumption.
Qed.


(*** Instantiating a field in a spec ***)

(* a refinement using the idFM FieldMap *)
Inductive IdRefinement {flds} (spec : Spec (flds:=flds)) : Type :=
| mkIdRefinement (spec' : Spec (flds:=flds)) (ism : IsMorphism spec spec' idFM)
  : IdRefinement spec.

Definition IdRefinement_projSpec {flds} {spec} (idr : @IdRefinement flds spec) :
  Spec (flds:=flds) :=
  match idr with
    | mkIdRefinement spec' _ => spec'
  end.

Definition IdRefinement_projIsM {flds} {spec} (idr : @IdRefinement flds spec) :
  IsMorphism spec (IdRefinement_projSpec idr) idFM :=
  match idr with
    | mkIdRefinement spec' ism => ism
  end.

(* proof that instantiating the first element of a spec yields a morphism *)
Lemma IsMorphism_instantiate_base f A a {flds} (spec : A -> Spec (flds:=flds)) :
  IsMorphism (Spec_ConsNone f A spec) (Spec_ConsSome f A a (spec a)) idFM.
  intros model ism; destruct ism.
  exists a; split;
  [ rewrite idFM_is_id | rewrite spec_map_id ]; assumption.
Qed.

(* instantiate the first element of a spec *)
Definition instantiate_field_base f {A} (a:A) {flds} (spec : A -> Spec (flds:=flds)) :
  IdRefinement (Spec_ConsNone f A spec) :=
  mkIdRefinement _ (Spec_ConsSome f A a (spec a))
                 (IsMorphism_instantiate_base _ _ _ _).

(*
Definition instantiate_field_base f {A} (a:A) {flds} (spec : A -> Spec (flds:=flds)) :
  { spec' : Spec (flds:=f :: flds) | IsMorphism (Spec_ConsNone f A spec) spec' idFM } :=
  existT _ (Spec_ConsSome f A a (spec a)) (IsMorphism_instantiate_base _ _ _ _).
*)

(* skip the first element of a ConsNone spec and instantiate the rest *)
Definition instantiate_field_None f A {flds} {spec : A -> Spec (flds:=flds)}
           (fn : forall a, IdRefinement (spec a)) :
  IdRefinement (Spec_ConsNone f A spec) :=
  mkIdRefinement _ (Spec_ConsNone f A (fun a => IdRefinement_projSpec (fn a)))
         (IsMorphism_ConsNone
            f A spec _ idFM
            (fun a => IdRefinement_projIsM (fn a))).

(*
Definition instantiate_field_None f A {flds} {spec : A -> Spec (flds:=flds)}
  (fn : forall a, { spec' : Spec (flds:=flds) |
                    IsMorphism (spec a) spec' idFM }) :
  { spec' : Spec (flds:=f :: flds) | IsMorphism (Spec_ConsNone f A spec) spec' idFM } :=
  existT _ (Spec_ConsNone f A (fun a => projT1 (fn a)))
         (IsMorphism_ConsNone
            f A spec _ idFM
            (fun a => projT2 (fn a))).
*)

(* skip the first element of a ConsSome spec and instantiate the rest *)
Definition instantiate_field_Some f A a {flds} {spec : Spec (flds:=flds)}
  (rest : IdRefinement spec) :
  IdRefinement (Spec_ConsSome f A a spec) :=
  mkIdRefinement _ (Spec_ConsSome f A a (IdRefinement_projSpec rest))
                 (IsMorphism_ConsSome f A a spec _ _ (IdRefinement_projIsM rest)).

(*
Definition instantiate_field_Some f A a {flds} {spec : Spec (flds:=flds)}
  (rest : { spec' : Spec (flds:=flds) | IsMorphism spec spec' idFM }) :
  { spec' : Spec (flds:=f :: flds) | IsMorphism (Spec_ConsSome f A a spec) spec' idFM } :=
  existT _ (Spec_ConsSome f A a (projT1 rest))
         (IsMorphism_ConsSome f A a spec _ _ (projT2 rest)).
*)

Definition test_spec_fun :=
  Spec_ConsNone "T"%string Set (fun T =>
  Spec_ConsNone "f"%string (T -> T) (fun f =>
  Spec_Nil)).

Definition test_spec_fun2 : Refinement test_spec_fun.
  assert (IdRefinement test_spec_fun) as H; [ | end_refine ].
  unfold test_spec_fun.
  apply instantiate_field_None; intro T.
  apply (instantiate_field_base "f"%string ((fun X (x:X) => x) T)).
Qed.

(* A helper tactic which repeatedly tries to apply instantiate_field_* above *)
Ltac instantiate_helper f fs val :=
  compute;
  lazymatch goal with
    | |- (IdRefinement (Spec_ConsNone f ?A ?rest)) =>
      lazymatch (eval compute in fs) with
        | nil => apply (instantiate_field_base f val)
        | _ => fail "Could not apply all supplied fields!"
      end
    | |- (IdRefinement (Spec_ConsNone ?f_cur ?A ?rest)) =>
      lazymatch (eval compute in fs) with
        | (f_cur :: ?fs_rest) =>
          let var := fresh "a" in
          apply instantiate_field_None; intro var;
          instantiate_helper f fs_rest (val var)
        | _ =>
          let var := fresh "a" in
          apply instantiate_field_None; intro var;
          instantiate_helper f fs val
      end
    | |- (IdRefinement (Spec_ConsSome ?f_cur ?A ?a ?rest)) =>
      lazymatch (eval compute in fs) with
        | (f_cur :: ?fs_rest) =>
          apply instantiate_field_Some;
          instantiate_helper f fs_rest (val a)
        | _ =>
          apply instantiate_field_Some;
          instantiate_helper f fs val
      end
    | |- _ => fail "instantiate_helper: not an IdRefinement goal!"
  end.
(*
  repeat (apply (instantiate_field_base f val) ||
          apply instantiate_field_None ||
          apply instantiate_field_Some).
*)

Ltac instantiate_helper_debug f fs val :=
  compute;
  lazymatch goal with
    | |- (IdRefinement (Spec_ConsNone f ?A ?rest)) =>
      lazymatch (eval compute in fs) with
        | nil => apply (instantiate_field_base f val)
        | _ => fail "Could not apply all supplied fields!"
      end
    | |- (IdRefinement (Spec_ConsNone ?f_cur ?A ?rest)) =>
      lazymatch (eval compute in fs) with
        | (f_cur :: ?fs_rest) =>
          let var := fresh "a" in
          apply instantiate_field_None; intro var;
          instantiate_helper_debug f fs_rest (val var)
        | _ =>
          let var := fresh "a" in
          apply instantiate_field_None; intro var;
          instantiate_helper_debug f fs val
      end
    | |- (IdRefinement (Spec_ConsSome ?f_cur ?A ?a ?rest)) =>
      lazymatch (eval compute in fs) with
        | (f_cur :: ?fs_rest) =>
          apply instantiate_field_Some;
          instantiate_helper_debug f fs_rest (val a)
        | _ =>
          apply instantiate_field_Some;
          instantiate_helper_debug f fs val
      end
    | |- _ => idtac "instantiate_helper_debug: not an IdRefinement goal!"
  end.

(* The tactic itself *)
Ltac instantiate_field f fs val :=
  lazymatch goal with
    | |- Refinement ?spec =>
      let H := fresh "H" in
      let ism := fresh "isMorph" in
      assert (IdRefinement spec) as H; [ instantiate_helper f fs val | ];
      destruct H as [ spec' ism ];
      apply_morphism (mkMorphism spec spec' idFM ism)
    | _ => fail "Not a refinement goal!"
  end.

(* Debugging version, which does not call instantiate_helper *)
Ltac instantiate_field_start :=
  lazymatch goal with
    | |- Refinement ?spec =>
      let H := fresh "H" in
      let ism := fresh "isMorph" in
      assert (IdRefinement spec) as H; [ | end_refine ]
    | _ => fail "Not a refinement goal!"
  end.

Ltac instantiate_field_debug f fs val :=
  lazymatch goal with
    | |- Refinement ?spec =>
      let H := fresh "H" in
      let ism := fresh "isMorph" in
      assert (IdRefinement spec) as H;
        [ instantiate_helper_debug f fs val | ]
    | _ => fail "Not a refinement goal!"
  end.

Definition test_spec1 :=
  Spec_ConsSome "T"%string Set nat (
  Spec_ConsNone "f"%string (nat -> nat) (fun f =>
  Spec_Nil)).

(* Instance string_FieldType : FieldType string := string_dec. *)

Definition test_spec2 : Refinement test_spec1.
  instantiate_field "f"%string ([]:list string) (fun (x:nat) => x).
  end_refine.
Defined.

Eval compute in (refinementSpec test_spec2).


Definition test_spec3 :=
  Spec_ConsNone "T"%string Set (fun T =>
  Spec_ConsNone "f"%string (T -> T) (fun f =>
  Spec_Nil)).

(* Instance string_FieldType : FieldType string := string_dec. *)

Definition test_spec4 : Refinement test_spec3.
  instantiate_field "f"%string (["T"%string]) (fun T (x:T) => x).
  end_refine.
Defined.

Eval compute in (refinementSpec test_spec4).


  instantiate_helper_debug "f"%string fs (fun X (x:X) => x). *)
  (* apply instantiate_field_None. *)
  instantiate_field_start.
  compute. apply instantiate_field_None.
  let my_fs := (eval compute in fs) in
  lazymatch goal with
    | |- (IdRefinement (Spec_ConsNone ?f_cur ?A ?rest)) =>
      lazymatch my_fs with
        | (f_cur :: ?fs_rest) =>
          let var := fresh "a" in
          apply instantiate_field_None; intro var
        | _ => fail "aaaaahhhhh2"
      end
  end.


  end_refine.
Defined.

Eval compute in (refinementSpec test_spec4).


  instantiate_field_debug.
  compute -[IsMorphism].
  lazymatch eval compute in test_spec1 with
    | { spec' : @Spec ?flds
         | IsMorphism (Spec_ConsSome ?f_cur ?A ?a ?rest) spec' idFM } =>
      fail "aaaahhhh"
  end.


  instantiate_field "f"%string ([]:list string) (fun (x:nat) => x).
  (*
  unfold test_spec1.
  lazymatch goal with
    | |- { spec' : @Spec ?flds
         | IsMorphism (Spec_ConsSome ?f_cur ?A ?a ?rest) spec' idFM } =>
      fail "aaaahhhh"
  end. *)
  lazymatch goal with
    | |- ?gl => let gl_eval := (eval compute in gl) in assert gl_eval
  end.

  let foo := eval compute in test_spec1 in assert (foo=foo).
  lazymatch eval compute in test_spec1 with
    | { spec' : @Spec ?flds
         | IsMorphism (Spec_ConsSome ?f_cur ?A ?a ?rest) spec' idFM } =>
      fail "aaaahhhh"
  end.
  instantiate_field "f"%string ([]:list string) (fun (x:nat) => x).
  end_refine.
Qed.

Definition test_spec_fun :=
  Spec_ConsNone "T" Set (fun T =>
  Spec_ConsNone "f" (T -> T) (fun f =>
  Spec_Nil)).

(* Set Ltac Debug. *)

Definition test_spec_id : Refinement test_spec_fun.
  assert ({ spec' : @Spec ["T"%string; "f"%string ] | IsMorphism test_spec_fun spec' idFM }) as H.
  instantiate_helper ("T"%string) (fun (x:nat) => x).

  instantiate_field ("f"%string) (fun T (x:T) => x).

Eval compute in (get_fields test_spec_fun).

Definition test_spec_id : Refinement test_spec_fun.
  assert ({ spec' : @Spec ["T"%string; "f"%string ] | IsMorphism test_spec_fun spec' idFM }) as H.
  apply instantiate_field_None; intro a.
  apply (instantiate_field_base (fun x => x)).
  destruct H as [ spec' ismorph ]; apply_morphism (mkMorphism _ _ _ ismorph).
  end_refine.
Defined.

Eval compute in (refinementSpec test_spec_id).



Definition test_spec_id :=
  Spec_ConsNone "T" Set (fun T =>
  Spec_ConsSome "idT" (T -> T) (fun t => t)
  Spec_Nil).

Definition test_spec_id_nat :=
  Spec_ConsSome "T" Set nat (
  Spec_ConsSome "idT" (nat -> nat) (fun t => t)
  Spec_Nil).

(* FIXME: cannot get type-class resolution to work here... *)
(*
Section instantiation.

  Class InstantiatesTo
        {flds1} (spec1 : Spec (flds:=flds1))
        {flds2} (spec2 : Spec (flds:=flds2)) : Prop :=
    instantiation_ismorph_id : IsMorphism spec1 spec2 idFM.

  Variables (flds:list string) (fld:string) (A:Type) (a:A)
            (spec:A -> Spec (flds:=flds)).

  Global Instance InstantiatesTo_Base :
    InstantiatesTo (Spec_ConsNone fld A spec) (Spec_ConsSome fld A a (spec a)).
  intros model ism; destruct ism.
  exists a; split;
  [ rewrite idFM_is_id | rewrite spec_map_id ]; assumption.
  Qed.

  (*
  Definition test1 :
    InstantiatesTo (Spec_ConsNone fld A spec) (Spec_ConsSome fld A a (spec a))
    := instantiation_ismorph_id.
   *)

End instantiation.
*)


(*
Program Definition instantiate_helper_step_ConsNone
           f A {flds} (spec : A -> Spec (flds:=flds))
           (F : forall a,
                  { spec' : Spec (flds:=flds) & IsMorphism (spec a) spec' id }) :
  { spec' : Spec (flds:= f :: flds)
                 & IsMorphism (Spec_ConsNone f A spec) spec' id } :=
  existT (fun spec' => IsMorphism _ spec' id)
         ({# f ::: A ; a => projT1 (F a) #})
         (fun model2 ism2 =>
            existT2 (fun _ => _) (fun _ => _) model2
                    _ _).
Obligation 1.
apply (IsModel_ConsNone)

  apply (match )

Definition instantiate_helper_step_ConsSome
           f A a {flds} (spec : A -> Spec (flds:=flds)) :
  { spec' : Spec (flds:= f :: flds) & IsMorphism (Spec_ConsNone f A spec) spec' id } :
*)

Ltac instantiate_field f val :=
  match goal with
    | |- Refinement ?flds ?spec =>
      let H := fresh "H" in
      let spec' := fresh "spec" in
      let ism := fresh "isMorph" in
      assert ({ spec' : Spec (flds:=flds) | IsMorphism spec spec' id }) as H; [ instantiate_helper f val spec | ];
      destruct H as [ spec' ism ];
      apply (apply_morphism (mkMorphism spec spec' id ism))
    | _ => fail "Not a refinement goal!"
  end.
