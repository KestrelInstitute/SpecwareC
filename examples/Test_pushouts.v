
Add LoadPath "../theories" as Specware.
Require Import Specware.SpecwareC.

(* Base spec contains two natural numbers, n and m *)
Definition base : Spec :=
  Spec_Cons
    "n" nat Pred_Trivial
    (fun n n__proof =>
       Spec_Cons
         "m" nat Pred_Trivial
         (fun m m__proof => Spec_Axioms nil)).

(* spec1 contains just the natural nmber n *)
Definition spec1 : Spec :=
  Spec_Cons "n" nat Pred_Trivial (fun n n__proof => Spec_Axioms nil).

(* Interpretation that sets m to be 2 *)
Definition interp1 : Interpretation base spec1 :=
  fun model =>
    match model with
      | opCons n n__proof I =>
        opCons n n__proof (opCons (oppred:=Pred_Trivial) 2 I I)
    end.

(* spec2 contains just the natural nmber m *)
Definition spec2 : Spec :=
  Spec_Cons "m" nat Pred_Trivial (fun m m__proof => Spec_Axioms nil).

(* Interpretation that sets n to be 1 *)
Definition interp2 : Interpretation base spec2 :=
  fun model =>
    match model with
      | opCons m m__proof I =>
        opCons (oppred:=Pred_Trivial) 1 I (opCons m m__proof I)
    end.

(* Now: find a pushout of interp1 and interp2 *)
Definition pushout12__destruct : Pushout interp1 interp2.
  eapply (Build_Pushout
            _ _ _ interp1 interp2 ?[__spec]
            (interp_compose
               (?[destruct__helper] : Interpretation ?__spec ?__spec)
               (fun model => (opCons ?[n] ?[n__proof] I) : spec_model spec1)
               )
            (interp_compose
               ?destruct__helper
               (fun model => (opCons ?[m] ?[m__proof] I) : spec_model spec2)
               )).
  intro model.
  unify (interp1 (opCons ?n ?n__proof I))
        (interp2 (opCons ?m ?m__proof I)).
  instantiate (s4:=Spec_Axioms nil).
  instantiate (destruct__helper:=(fun model =>
                                    match model with
                                      | I => I
                                    end)).
  reflexivity.
Defined.


Ltac build_spec_model_evars n :=
  lazymatch goal with
    | |- spec_model (Spec_Axioms ?axioms) =>
      change (conjoin_axioms axioms); build_spec_model_evars n
    | |- conjoin_axioms nil =>
      apply I
    | |- conjoin_axioms (cons (specAxiom ?ax_id ?P) nil) =>
      raw_evar ax_id P
               (fun evar =>
                  set_evar_property sort_hint evar n;
                  set_evar_property spec_axiom_p evar true;
                  exact evar)
    | |- conjoin_axioms (cons (specAxiom ?ax_id ?P) ?rest) =>
      change (P /\ conjoin_axioms rest);
      raw_evar ax_id P
               (fun evar =>
                  set_evar_property sort_hint evar n;
                  set_evar_property spec_axiom_p evar true;
                  apply (conj evar); build_spec_model_evars (n+1))
      (*
      evar (ax:P);
      apply (conj ?ax); build_spec_model_evars *)
    | |- spec_model (Spec_Cons ?f ?T ?oppred ?rest_f) =>
      change (OpCons T oppred (fun t pf => spec_model (rest_f t pf)));
      raw_evar
        f T
        (fun evar1 =>
           raw_evar (append f "__proof")
                    (sats_op_pred oppred evar1)
                    (fun evar2 =>
                       set_evar_property sort_hint evar1 n;
                       set_evar_property spec_axiom_p evar1 false;
                       set_evar_property sort_hint evar2 (n+1);
                       set_evar_property spec_axiom_p evar2 false;
                       apply (opCons evar1 evar2);
                       build_spec_model_evars (n+2)))
      (* eapply (opCons ?[?t] ?[?pf]); build_spec_model_evars *)
    | |- spec_model ?s =>
      let s_hnf := (eval hnf in s) in
      progress (change (spec_model s_hnf)); build_spec_model_evars n
  end.

(* We need our own "smart" version of the unify tactic, because Coq's built-in
one does not always seem to work correctly... *)
Ltac unify_models model1 model2 :=
  let model1_hnf := (eval hnf in model1) in
  let model2_hnf := (eval hnf in model2) in
  lazymatch model1_hnf with
    | opCons ?t1 ?pf1 ?model1' =>
      lazymatch model2_hnf with
        | opCons ?t2 ?pf2 ?model2' =>
          unify t1 t2; unify pf1 pf2;
          unify_models model1' model2'
      end
    | _ => unify model1_hnf model2_hnf
  end.

Ltac pushout_tac :=
  lazymatch goal with
    | |- @Pushout ?spec ?spec1 ?spec2 ?interp1 ?interp2 =>
      (raw_evar
         "__spec"%string Spec
         (fun evar =>
            refine (Build_Pushout _ _ _ interp1 interp2 ?__spec _ _ _)));
      [ intro model; build_spec_model_evars 0
      | intro model; build_spec_model_evars 0
      | intro model;
        lazymatch goal with
          | |- ?m1 = ?m2 =>
            unify_models m1 m2
            (* instantiate_spec ?__spec; apply eq_refl *)
        end ]
  end.


Definition pushout12 : Pushout interp1 interp2.
  pushout_tac.
  instantiate (__spec:=Spec_Axioms nil).
  apply eq_refl.
Defined.



(* More complex example: the pushout of divide-and-conquer and sorting *)

Require Import List.
Import ListNotations.
Require Import Coq.Arith.Peano_dec.
Require Import Recdef.
Require Import Coq.Program.Wf.


Definition dnc_spec1 : Spec :=
  Spec_Cons
    "D" Type Pred_Trivial
    (fun D _ =>
       Spec_Cons
         "R" Type Pred_Trivial
         (fun R _ =>
            Spec_Cons
              "IO" (D -> R -> Prop) Pred_Trivial
              (fun IO _ => 
                 Spec_Cons
                   "solve" (D -> R) Pred_Trivial
                   (fun solve _ =>
                      Spec_Axioms [specAxiom "solve_correct"
                                             (forall d, IO d (solve d))])))).


Definition dnc_spec2 : Spec :=
  Spec_Cons
    "D" Type Pred_Trivial
    (fun D _ =>
       Spec_Cons
         "R" Type Pred_Trivial
         (fun R _ =>
            Spec_Cons
              "IO" (D -> R -> Prop) Pred_Trivial
              (fun IO _ =>
                 Spec_Cons
                   "smaller" (D -> D -> Prop) (Pred_Fun (fun x => well_founded x))
                   (fun smaller smaller__proof =>
                      Spec_Cons
                        "primitive" (D -> bool) Pred_Trivial
                        (fun primitive _ =>
                           Spec_Cons
                             "direct_solve" (D -> R) Pred_Trivial
                             (fun direct_solve _ =>
                                Spec_Cons
                                  "decompose" (D -> D * D)
                                  (Pred_Fun (fun decompose =>
                                               (forall d,
                                                  primitive d = false ->
                                                  smaller (fst (decompose d)) d /\
                                                  smaller (snd (decompose d)) d)))
                                  (fun decompose decompose__proof =>
                                     Spec_Cons
                                       "compose" (R -> R -> R) Pred_Trivial
                                       (fun compose _ =>
                                          Spec_Axioms
                                            [ specAxiom
                                                "direct_solve_correct"
                                                (forall d, primitive d = true ->
                                                           IO d (direct_solve d));
                                              specAxiom
                                                "solve_soundness"
                                                (forall d z1 z2,
                                                   IO (fst (decompose d)) z1 ->
                                                   IO (snd (decompose d)) z2 ->
                                                   IO d (compose z1 z2))
                                            ]
    )))))))).

Definition bool_dec (b1 b2:bool) : {b1=b2} + {b1<>b2}.
  decide equality.
Defined.

Fixpoint solve_def (D R : Type)
        (smaller : D -> D -> Prop)
        (primitive: D -> bool) (direct_solve : D -> R)
        (decompose :
           forall d,
             {d1 : D & {d2 : D &
                             primitive d = false ->
                             smaller d1 d /\
                             smaller d2 d }})
        (compose : R -> R -> R)
        (d:D)
        (acc: Acc smaller d) : R :=
  match bool_dec (primitive d) false with
    | right _ => direct_solve d
    | left not_prim =>
      let (d1, rest) := decompose d in
      let (d2, smaller_d12) := rest in
      match acc with
        | Acc_intro _ acc_f =>
          (compose
             (solve_def D R smaller primitive direct_solve decompose compose
                        d1 (acc_f d1 (proj1 (smaller_d12 not_prim))))
             (solve_def D R smaller primitive direct_solve decompose compose
                        d2 (acc_f d2 (proj2 (smaller_d12 not_prim)))))
      end
  end.

Lemma solve_def_correct (D R : Type)
      (IO : D -> R -> Prop)
      (smaller : D -> D -> Prop) (smaller__proof : well_founded smaller)
      (primitive: D -> bool) (direct_solve : D -> R)
      (decompose : D -> D*D)
      (decompose__proof :
         forall (d:D), primitive d = false ->
                       smaller (fst (decompose d)) d /\
                       smaller (snd (decompose d)) d)
      (compose : R -> R -> R)
      (direct_solve_correct :
         forall d, primitive d = true ->
                   IO d (direct_solve d))
      (solve_soundness :
         forall d z1 z2,
           IO (fst (decompose d)) z1 ->
           IO (snd (decompose d)) z2 ->
           IO d (compose z1 z2))
      (d:D) :
  IO d (solve_def D R smaller primitive direct_solve
                  (fun d =>
                     (match decompose d as res return
                            (primitive d = false ->
                             smaller (fst res) d /\ smaller (snd res) d) ->
                            {d1:D & {d2:D & _}}
                      with
                        | pair d1 d2 =>
                          fun pf =>
                            existT _ d1 (existT _ d2 pf)
                      end)
                       (decompose__proof d))
                  compose d (smaller__proof d)).
  revert d; apply (well_founded_ind smaller__proof); intros d IH.
  destruct (smaller__proof d).
  unfold solve_def; fold solve_def.
  destruct (bool_dec (primitive d) false);
    [ | apply direct_solve_correct;
        destruct (primitive d);
        [ reflexivity | elimtype False; apply (n eq_refl) ]].
  admit.
Defined.  


(*
Fixpoint solve_def  (D R : Type)
        (smaller : D -> D -> Prop)
        (primitive: D -> bool) (direct_solve : D -> R)
        (decompose :
           forall (d:D),
           {res : D * D | primitive d = false ->
                          smaller (fst res) d /\ smaller (snd res) d})
        (compose : R -> R -> R)
        (d:D)
        (acc: Acc smaller d) : R.
  case_eq (primitive d).
  intro; apply (direct_solve d).
  intro not_prim.
  destruct (decompose d) as [ res res_pf ]; destruct res as [ d1 d2 ].
  destruct acc as [ acc_f ].
  apply (compose
           (solve_def D R smaller primitive direct_solve decompose compose
                      d1 (acc_f d1 (proj1 (res_pf not_prim))))
           (solve_def D R smaller primitive direct_solve decompose compose
                      d2 (acc_f d2 (proj2 (res_pf not_prim))))).
Defined.
*)

Program Definition dnc_interp : Interpretation dnc_spec1 dnc_spec2 :=
  fun model =>
    match model with
      | opCons
          D D__proof
          (opCons
             R R__proof
             (opCons
                IO IO__proof
                (opCons
                   smaller smaller__proof
                   (opCons
                      primitive primitive__proof
                      (opCons
                         direct_solve direct_solve__proof
                         (opCons
                            decompose decompose__proof
                            (opCons
                               compose compose__proof
                               (conj direct_solve_correct solve_soundness))))))))
        =>
        opCons
          (oppred:=Pred_Trivial) D D__proof
          (opCons
             (oppred:=Pred_Trivial) R R__proof
             (opCons
                (oppred:=Pred_Trivial) IO IO__proof
                (opCons
                   (oppred:=Pred_Trivial)
                   (fun d =>
                      solve_def D R smaller primitive direct_solve
                                (fun d =>
                                   (match decompose d as res return
                                          (primitive d = false ->
                                           smaller (fst res) d /\ smaller (snd res) d) ->
                                          {d1:D & {d2:D & _}}
                                    with
                                      | pair d1 d2 =>
                                        fun pf =>
                                          existT _ d1 (existT _ d2 pf)
                                    end)
                                     (decompose__proof d))
                                compose d (smaller__proof d))
                   I
                   _
          )))
    end.
Next Obligation.
  apply solve_def_correct; assumption.
Defined.



Fixpoint sorted (l: list nat) : Prop :=
  match l with
    | [] => True
    | x::l' =>
      (match l' with
         | [] => True
         | y::_ => x <= y /\ sorted l'
       end)
  end.

Definition permOf (l1 l2: list nat) : Prop :=
  forall x, count_occ eq_nat_dec l1 x = count_occ eq_nat_dec l2 x.


Definition sorting_spec : Spec :=
  Spec_Cons
    "sort" (list nat -> list nat) Pred_Trivial
    (fun sort _ =>
       Spec_Axioms [specAxiom "sort_correct"
                              (forall l, sorted (sort l) /\ permOf l (sort l))]).

Definition dnc_sorting_interp : Interpretation dnc_spec1 sorting_spec :=
  fun model =>
    match model with
      | opCons sort sort__proof sort_correct =>
        opCons
          (oppred:=Pred_Trivial) (list nat : Type) I
          (opCons
             (oppred:=Pred_Trivial) (list nat : Type) I
             (opCons
                (oppred:=Pred_Trivial) (fun lin lout => sorted lout /\ permOf lin lout) I
                (opCons
                   (oppred:=Pred_Trivial) sort sort__proof
                   sort_correct)))
    end.


Definition pushout_dnc_sorting : Pushout dnc_sorting_interp dnc_interp.
  pushout_tac.
  Show Existentials.

  lazymatch goal with
    | |- @Pushout ?spec ?spec1 ?spec2 ?interp1 ?interp2 =>
      (raw_evar
         "__spec"%string Spec
         (fun evar =>
            refine (Build_Pushout _ _ _ interp1 interp2 ?__spec _ _ _)));
      [ intro model; build_spec_model_evars
      | intro model; build_spec_model_evars
      | intro model;
        lazymatch goal with
          | |- ?m1 = ?m2 =>
            (* unify m1 m2 *) idtac
            (* instantiate_spec ?__spec; apply eq_refl *)
        end ]
  end.


  lazymatch goal with
    | |- spec_model ?s =>
      let s_hnf := (eval hnf in s) in
      progress (change (spec_model s_hnf))
  end.

  lazymatch goal with
    | |- spec_model (Spec_Cons ?f ?T ?oppred ?rest_f) =>
      change (OpCons T oppred (fun t pf => spec_model (rest_f t pf)));
      raw_evar
        f T
        (fun evar1 =>
           raw_evar (append f "__proof") (sats_op_pred oppred evar1)
                    (fun evar2 =>
                       apply (opCons evar1 evar2)))
  end.

  lazymatch goal with
    | |- spec_model (Spec_Cons ?f ?T ?oppred ?rest_f) =>
      raw_evar
        f T
        (fun evar1 =>
           raw_evar (append f "__proof") (sats_op_pred oppred evar1)
                    (fun evar2 =>
                       apply (opCons evar1 evar2)))
  end.

  lazymatch goal with
    | |- spec_model (Spec_Axioms nil) =>
      apply I
    | |- conjoin_axioms nil =>
      apply I
    | |- spec_model (Spec_Axioms (cons (specAxiom ?ax_id ?P) nil)) =>
      evar (ax:P); exact ?ax
    | |- conjoin_axioms (cons (specAxiom ?ax_id ?P) nil) =>
      evar (ax:P); exact ?ax
    | |- spec_model (Spec_Axioms (cons (specAxiom ?ax_id ?P) ?rest)) =>
      raw_evar ax_id P (fun evar => apply (conj evar))
      (*
      evar (ax:P);
      apply (conj ?ax); build_spec_model_evars *)
    | |- conjoin_axioms (cons (specAxiom ?ax_id ?P) ?rest) =>
      raw_evar ax_id P (fun evar => apply (conj evar))
      (*
      evar (ax:P);
      apply (conj ?ax); build_spec_model_evars *)
    | |- spec_model (Spec_Cons ?f ?T ?oppred ?rest_f) =>
      raw_evar
        f T
        (fun evar1 =>
           raw_evar (append f "__proof") (sats_op_pred oppred evar1)
                    (fun evar2 =>
                       apply (opCons evar1 evar2);
                       build_spec_model_evars))
      (* eapply (opCons ?[?t] ?[?pf]); build_spec_model_evars *)
    | |- spec_model ?s =>
      let s_hnf := (eval hnf in s) in
      progress (change (spec_model s_hnf)); build_spec_model_evars
  end.


  build_spec_model_evars.

  pushout_tac.

