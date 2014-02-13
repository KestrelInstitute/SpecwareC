
(*** Tactics for Refinement ***)

Add LoadPath "." as Specware.
Require Import Specware.Util.
Require Export Specware.Base.

Require Export Coq.Logic.Eqdep.


(*** Refinements and helper defs ***)

(* a Refinement of a spec is another spec and a morphism to it *)
Inductive Refinement {flds} (spec : Spec (flds:=flds)) : Type :=
| mkRefinement {flds'} (spec' : Spec (flds:=flds')) (morph : Morphism spec spec')
  : Refinement spec.

(* An existential type for a spec that hides the fields when printing *)
Inductive SomeSpec : Type :=
| mkSomeSpec {flds} (spec : Spec (flds:=flds)) : SomeSpec.

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


(*** A Refinement step that applies an arbitrary morphism ***)

(* Applying a morphism to a refinement goal *)
Definition apply_morphism_fun {flds1} (spec1 : Spec (flds:=flds1))
           {flds2} (spec2 : Spec (flds:=flds2))
           (m12 : Morphism spec1 spec2) :
  Refinement spec2 ->
  Refinement spec1.
  intro ref2; destruct ref2 as [ flds3 spec3 m23 ].
  apply (mkRefinement _ spec3);
  apply (mcompose m12 m23).
Qed.

(* the tactic version; mostly used by other tactics *)
Ltac apply_morphism morph :=
  apply (apply_morphism_fun _ _ morph).


(*** Instantiating a field in a spec ***)

Lemma IsModel_SomeToNone f A a {flds} (spec : A -> Spec (flds:=flds)) model :
  IsModel ({# f ::: A := a ; spec a #}) model ->
  IsModel ({# f ::: A ;  x =>  spec x #}) model.
  revert f A a flds spec model.
  assert
    (forall flds (spec : Spec (flds:=flds)) model,
       IsModel spec model ->
       forall f A a flds' (spec' : A -> Spec (flds:= flds')),
       existT (@Spec) flds spec
       = existT (@Spec) (cons f flds') ({# f ::: A := a ; spec' a #}) ->
       exists model',
         existT _ flds model = existT _ (cons f flds') model' /\
         IsModel ({# f ::: A ;  x =>  spec' x #}) model').
  intros flds spec model ism; induction ism; intros.
  discriminate H.
  discriminate H.
  injection H; intros.
  revert a0 spec' H H0 H2; rewrite <- H1; rewrite <- H3; rewrite <- H6;
  intros.
  exists (Model_Cons f A a model); split;
  [ reflexivity | apply IsModel_ConsNone ].
  rewrite <- (inj_pair2 _ _ _ _ _ H2) in H; injection H; intro.
  rewrite <- (inj_pair2 _ _ _ _ _ H7); assumption.
  intros;
  destruct (H _ _ _ H0 f A a _ spec eq_refl) as [ model' H1 ];
  destruct H1 as [ e ism' ].
  rewrite (inj_pair2 _ _ _ _ _ e); assumption.
Qed.

Definition instantiate_helper_base_fun
        f A a {flds} (spec : A -> Spec (flds:=flds)) :
  { spec' : Spec (flds:= f :: flds) & IsMorphism (Spec_ConsNone f A spec) spec' id } :=
  existT (fun spec' => IsMorphism _ spec' id) (Spec_ConsSome f A a (spec a))
         (fun model2 ism2 =>
            existT2 (fun _ => _) (fun _ => _) model2
                    (IsModel_SomeToNone _ _ _ _ _ ism2)
                    (SuperModel_map_id _)).


Lemma IsMorphism_id_ConsNone f A {flds} (spec1 : A -> Spec (flds:=flds))
      (spec2 : A -> Spec (flds:=flds)) :
  (forall a, IsMorphism (spec1 a) (spec2 a) id) ->
  IsMorphism ({# f ::: A ; a => spec1 a #}) ({# f ::: A ; a => spec2 a #}) id.
  intros ismorph model ism; exists model; [ | apply SuperModel_map_id ].
  inversion ism.
  rewrite <- (inj_pair2 _ _ _ _ _ H4).
  apply IsModel_ConsNone.
  assert (forall a, spec2 a = spec0 a);
    [ rewrite (inj_pair2 _ _ _ _ _ (inj_pair2 _ _ _ _ _ H3)); intro; reflexivity | ].
  rewrite <- (H5 a) in H0.
  destruct (ismorph a model0 H0).

 assumption.

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
