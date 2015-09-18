
Add LoadPath "../theories" as Specware.
Require Import Specware.SpecwareC.

(* Base spec contains two natural numbers, n and m *)
Definition base : Spec :=
  Spec_Cons
    "n" nat
    (fun n =>
       Spec_Cons
         "m" nat
         (fun m => Spec_Axioms nil)).

(* spec1 contains just the natural nmber n *)
Definition spec1 : Spec :=
  Spec_Cons "n" nat (fun n => Spec_Axioms nil).

(* Interpretation that sets m to be 2 *)
Definition interp1 : Interpretation base spec1 :=
  fun model =>
    match model with
      | existT _ n I =>
        existT _ n (existT _ 2 I)
    end.

(* spec2 contains just the natural nmber m *)
Definition spec2 : Spec :=
  Spec_Cons "m" nat (fun m => Spec_Axioms nil).

(* Interpretation that sets n to be 1 *)
Definition interp2 : Interpretation base spec2 :=
  fun model =>
    match model with
      | existT _ m I =>
        existT _ 1 (existT _ m I)
    end.

(* Now: find a pushout of interp1 and interp2 *)
Definition pushout12__destruct : Pushout interp1 interp2.
  eapply (Build_Pushout
            _ _ _ interp1 interp2 ?[__spec]
            (interp_compose
               (?[destruct__helper] : Interpretation ?__spec ?__spec)
               (fun model => (existT _ ?[n] I) : spec_model spec1)
               )
            (interp_compose
               ?destruct__helper
               (fun model => (existT _ ?[m] I) : spec_model spec2)
               )).
  intro model.
  unify (interp1 (existT _ ?n I))
        (interp2 (existT _ ?m I)).
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
    | |- spec_model (Spec_Cons ?f ?T ?rest_f) =>
      change (@sigT T (fun t => spec_model (rest_f t)));
      raw_evar
        f T
        (fun evar =>
           set_evar_property sort_hint evar n;
           set_evar_property spec_axiom_p evar false;
           apply (existT _ evar);
           build_spec_model_evars (n+1))
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
    | existT _ ?t1 ?model1' =>
      lazymatch model2_hnf with
        | existT _ ?t2 ?model2' =>
          unify t1 t2; unify_models model1' model2'
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


(*** New idea: use record types! ***)

Module rec_base.
Record rec_base : Type := { n:nat; m:nat }.
End rec_base.

Module rec_1.
Record rec_1 : Type := { n:nat }.
End rec_1.

Module rec_2.
Record rec_2 : Type := { m:nat }.
End rec_2.

Definition rec_interp1 (model: rec_1.rec_1) : rec_base.rec_base :=
  match model with
    | {| rec_1.n := n |} => {| rec_base.n := n; rec_base.m := 2 |}
  end.

Definition rec_interp2 (model: rec_2.rec_2) : rec_base.rec_base :=
  match model with
    | {| rec_2.m := m |} => {| rec_base.n := 1; rec_base.m := m |}
  end.

Record RPushout {R R1 R2} (i1: R1 -> R) (i2: R2 -> R) : Type :=
  {R' : Type;
   i1' : R' -> R1;
   i2' : R' -> R2;
   rpushout_pf : forall model', i1 (i1' model') = i2 (i2' model') }.

Module rpushout12.
Definition rpushout12__Pushout : RPushout rec_interp1 rec_interp2.
  (raw_evar
     "__R"%string Type
     (fun evar =>
        refine (Build_RPushout _ _ _ rec_interp1 rec_interp2 ?__R _ _ _)
      ;
      [ intro model;
        raw_evar "n"%string nat (fun evar => apply (rec_1.Build_rec_1 evar))
      | intro model;
        raw_evar "m"%string nat (fun evar => apply (rec_2.Build_rec_2 evar))
      | intro model;
        lazymatch goal with
          | |- ?m1 = ?m2 =>
            unify m1 m2
        end ])).
  (* instantiate_record_type ?__R. *)
  Record rpushout12__Record : Type := { }.
  instantiate (__R:=rpushout12__Record).
  apply eq_refl.
Defined.
End rpushout12.


Set Printing Universes.

Module rpushout_1_id.
Definition rpushout_1_id__Pushout : RPushout rec_interp1 id.
  (raw_evar
     "__R"%string Type
     (fun evar =>
        refine (Build_RPushout _ _ _ rec_interp1 id ?__R _ _ _)
      ;
      [ intro model;
        raw_evar "n"%string nat (fun evar => apply (rec_1.Build_rec_1 evar))
      | intro model;
        raw_evar "m"%string nat (fun evar => apply (rec_base.Build_rec_base evar))
      | intro model;
        lazymatch goal with
          | |- ?m1 = ?m2 =>
            unify m1 m2
        end ])).
  Show Existentials.
  Show Universes.
  (* instantiate_record_type ?__R. *)
  Record __R : Set := { m:nat }.
  instantiate (__R:=__R). instantiate (m:=m model).
  Show Universes.
  apply eq_refl.
  Show Universes.
(* Defined_Debug. *)
Defined.

Print rpushout_1_id__Pushout.
Check (let x := _ in let y := (rpushout_1_id__Pushout:x) in x).
Check RPushout.
End rpushout_1_id.


(* More complex example: the pushout of divide-and-conquer and sorting *)

Require Import List.
Import ListNotations.
Require Import Coq.Arith.Peano_dec.
Require Import Recdef.
Require Import Coq.Program.Wf.


Definition dnc_spec1 : Spec :=
  Spec_Cons
    "D" Type
    (fun D =>
       Spec_Cons
         "R" Type
         (fun R =>
            Spec_Cons
              "IO" (D -> R -> Prop)
              (fun IO => 
                 Spec_Cons
                   "solve" (D -> R)
                   (fun solve =>
                      Spec_Axioms [specAxiom "solve_correct"
                                             (forall d, IO d (solve d))])))).


Definition dnc_spec2 : Spec :=
  Spec_Cons
    "D" Type
    (fun D =>
       Spec_Cons
         "R" Type
         (fun R =>
            Spec_Cons
              "IO" (D -> R -> Prop)
              (fun IO =>
                 Spec_Cons
                   "smaller" (D -> D -> Prop)
                   (fun smaller =>
                      Spec_Cons
                        "smaller__proof" (well_founded smaller)
                        (fun smaller__proof =>
                           Spec_Cons
                             "primitive" (D -> bool)
                             (fun primitive =>
                                Spec_Cons
                                  "direct_solve" (D -> R)
                                  (fun direct_solve =>
                                     Spec_Cons
                                       "decompose" (D -> D * D)
                                       (fun decompose =>
                                          Spec_Cons
                                            "decompose__proof"
                                            (forall d,
                                               primitive d = false ->
                                               smaller (fst (decompose d)) d /\
                                               smaller (snd (decompose d)) d)
                                            (fun decompose__proof =>
                                               Spec_Cons
                                                 "compose" (R -> R -> R)
                                                 (fun compose =>
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
         )))))))))).

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
      | existT
          _ D
          (existT
             _ R
             (existT
                _ IO
                (existT
                   _ smaller
                   (existT
                      _ smaller__proof
                      (existT
                         _ primitive
                         (existT
                            _ direct_solve
                            (existT
                               _ decompose
                               (existT
                                  _ decompose__proof
                                  (existT
                                     _ compose
                                     (conj direct_solve_correct solve_soundness))))))))))
        =>
        existT
          _ D
          (existT
             _ R
             (existT
                _ IO
                (existT
                   _ (fun d =>
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
                   _
          )))
    end.
Next Obligation.
  apply solve_def_correct; assumption.
Defined.

Print dnc_interp.

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
    "sort" (list nat -> list nat)
    (fun sort =>
       Spec_Axioms [specAxiom "sort_correct"
                              (forall l, sorted (sort l) /\ permOf l (sort l))]).

Definition dnc_sorting_interp : Interpretation dnc_spec1 sorting_spec :=
  fun model =>
    match model with
      | existT _ sort sort_correct =>
        existT
          _ (list nat : Type)
          (existT
             _ (list nat : Type)
             (existT
                _ (fun lin lout => sorted lout /\ permOf lin lout)
                (existT
                   _ sort
                   sort_correct)))
    end.





Definition pushout_dnc_sorting : Pushout dnc_sorting_interp dnc_interp.
  pushout_tac.
  Show Existentials.
  Check [existT id _ ?smaller; existT id _ ?smaller__proof;
         existT id _ ?primitive; existT id _ ?primitive__proof;
        ].

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

