
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




Ltac apply_conj_helper evar :=
  apply (conj evar).

Ltac apply_opcons_helper2 evar1 evar2 :=
  apply (opCons evar1 evar2).

Ltac apply_opcons_helper1 f oppred evar1 :=
  raw_evar (append f "__proof") (sats_op_pred oppred evar1)
           (apply_opcons_helper2 evar1 False).

Ltac build_spec_model_evars :=
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
      raw_evar ax_id P apply_conj_helper
      (*
      evar (ax:P);
      apply (conj ?ax); build_spec_model_evars *)
    | |- conjoin_axioms (cons (specAxiom ?ax_id ?P) ?rest) =>
      raw_evar ax_id P (apply_conj_helper False)
      (*
      evar (ax:P);
      apply (conj ?ax); build_spec_model_evars *)
    | |- spec_model (Spec_Cons ?f ?T ?oppred ?rest_f) =>
      raw_evar f T (apply_opcons_helper1 f oppred False)
      (* eapply (opCons ?[?t] ?[?pf]); build_spec_model_evars *)
    | |- spec_model ?s =>
      let s_hnf := (eval hnf in s) in
      progress (change (spec_model s_hnf)); build_spec_model_evars
  end.

Ltac pushout_tac :=
  lazymatch goal with
    | |- @Pushout ?spec ?spec1 ?spec2 ?interp1 ?interp2 =>
      evar (__spec:Spec);
      (* raw_evar "__spec"%string Spec *)
      (refine (Build_Pushout _ _ _ interp1 interp2 ?__spec _ _ _));
      [ intro model; build_spec_model_evars
      | intro model; build_spec_model_evars
      | intro model (* ; apply eq_refl *) ]
  end.

Goal (True /\ True).
  raw_evar "foo"%string True (apply_conj_helper False).


Definition pushout12 : Pushout interp1 interp2.
  pushout_tac.
  apply eq_refl.
  Unshelve.
  apply (Spec_Axioms nil).
Defined.

Print pushout12.


  instantiate (__spec:=Spec_Axioms nil).

  unfold interp1. unfold interp2.
apply eq_refl.

  lazymatch goal with
    | |- @Pushout ?spec ?spec1 ?spec2 ?interp1 ?interp2 =>
      evar (__spec:Spec);
      refine (Build_Pushout _ _ _ interp1 interp2 ?__spec _ _ _); 
      [ intro model (* ; build_spec_model_evars *)
      | intro model (* ; build_spec_model_evars *)
      | ]
  end.

  lazymatch goal with
    | |- spec_model (Spec_Axioms nil) =>
      apply I
    | |- spec_model (Spec_Axioms (cons (specAxiom ?ax_id ?P) nil)) =>
      evar (ax:P); exact ?ax
    | |- spec_model (Spec_Axioms (cons (specAxiom ?ax_id ?P) ?rest)) =>
      evar (ax:P);
      apply (conj ?ax); build_spec_model_evars
    | |- spec_model (Spec_Cons ?f ?T ?oppred ?rest_f) =>
      evar (t:T); evar (pf:oppred ?t);
      apply (opCons ?t ?pf); intros
    | |- spec_model ?s =>
      let s_hnf := (eval hnf in s) in
      progress (change (spec_model s_hnf))
  end.

  evar (t:nat); evar (pf:Pred_Trivial ?t).
  apply (opCons ?t ?pf).

  apply (opCons ?t ?pf); intros.


  lazymatch goal with
    | |- spec_model (Spec_Axioms nil) =>
      apply I
    | |- spec_model (Spec_Axioms (cons (specAxiom ?ax_id ?P) nil)) =>
      evar (ax:P); exact ?ax
    | |- spec_model (Spec_Axioms (cons (specAxiom ?ax_id ?P) ?rest)) =>
      evar (ax:P);
      apply (conj ?ax); build_spec_model_evars
    | |- spec_model (Spec_Cons ?f ?T ?oppred ?rest_f) =>
      evar (t:T); evar (pf:oppred ?t);
      apply (opCons ?t ?pf); intros
    | |- spec_model ?s =>
      let s_hnf := (eval hnf in s) in
      progress (change (spec_model s_hnf))
  end.
  

  intro model. build_spec_model_evars.

  pushout_tac.

  evar (__spec:Spec);
  refine (Build_Pushout
            _ _ _ interp1 interp2 ?__spec
            _ _ _).
  intro model.

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



Ltac build_spec_model spec :=
  lazymatch spec with
    | Spec_Axioms nil =>
      uconstr:I
    | Spec_Axioms (cons (specAxiom ?ax_id ?P) nil) =>
      uconstr:?[pf]
    | Spec_Axioms (cons (specAxiom ?ax_id ?P) ?rest) =>
      let model' := build_spec_model rest in
      uconstr:(conj ?[pf] model')
    | Spec_Cons ?f ?T ?oppred ?rest_f =>
      let unused1 := evar (t:T) in
      let unused2 := evar (pf:oppred ?t) in
      let rest := (eval hnf in (rest_f ?t ?pf)) in
      let model' := uconstr:I (* build_spec_model rest *) in
      uconstr:(opCons ?t ?pf model')
  end.

Ltac pushout_tac :=
  idtac "foo";
  lazymatch goal with
    | |- @Pushout ?spec ?spec1 ?spec2 ?interp1 ?interp2 =>
      let f1 := type_term (fun model => $(build_spec_model spec1)$) in
      let f2 := type_term (fun model => $(build_spec_model spec2)$) in
      eapply (Build_Pushout _ _ _ interp1 interp2 ?[__spec] f1 f2);
      intro model
  end.

Definition pushout12 : Pushout interp1 interp2.
  let s1_hnf := (eval hnf in spec1) in
  let x := evar (t:nat) in
  let y := evar (pf:Pred_Trival ?t) in
  let model :=
  lazymatch s1_hnf with
    | Spec_Cons ?f ?T ?oppred ?rest_f => uconstr:(opCons ?t ?pf I)
  end in
  idtac model.


  let s1_hnf := (eval hnf in spec1) in
  let m := build_spec_model s1_hnf in
  idtac m.


  let s1_hnf := (eval hnf in spec1) in
  let m := build_spec_model s1_hnf in
  let f := uconstr:(fun model => m) in
  idtac f.


  let f := type_term (fun model => $(build_spec_model s1_hnf)$ : spec_model spec1) in
  idtac model.
  pushout_tac.

  match 

  let model1 := build_spec_model 
  eapply (Build_Pushout
            _ _ _ interp1 interp2 ?[__spec]
            (fun model =>
               

(opCons ?[n] ?[n__proof] I))
            (fun model => (opCons ?[m] ?[m__proof] I))).
  intro model.
  unify (interp1 (opCons ?n ?n__proof I))
        (interp2 (opCons ?m ?m__proof I)).
  instantiate (__spec:=Spec_Axioms nil).
  reflexivity.
Defined.

Print pushout12.
Eval compute in pushout12.

Definition pushout12' : Pushout interp1 interp2.
  eapply (Build_Pushout
            _ _ _ interp1 interp2 ?[Spec]
            (fun model => (opCons ?[n] ?[n__proof] I))
            (fun model => (opCons ?[m] ?[m__proof] I))).
  intro model.
  unify (interp1 (opCons ?n ?n__proof I))
        (interp2 (opCons ?m ?m__proof I)).
  instantiate (Spec:=Spec_Axioms nil).
  reflexivity.
Defined.

