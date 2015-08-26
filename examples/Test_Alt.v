Add LoadPath "../theories" as Specware.
Require Import Specware.Spec.

Fixpoint spec_model2 spec : Type :=
  match spec with
    | Spec_Axioms axioms => conjoin_axioms axioms
    | Spec_ConsOp f T oppred rest =>
      { t : T & {pf: oppred t & spec_model2 (rest t pf) } }
  end.

Record refinement : Type :=
  {rspec : Spec;
   rinterps : list (spec_model2 rspec -> { P:Prop | P } ) }.

Require Import Coq.Arith.Plus.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma add_axiom name tp axioms : conjoin_axioms (axioms ++ [ax_pair name tp]) ->
                                 conjoin_axioms axioms.
  induction axioms; intro H.
  apply I.
  destruct axioms.
  destruct H; assumption.
  destruct H; split.
  assumption.
  apply IHaxioms; assumption.
Qed.
Arguments add_axiom name%string tp axioms _.

Definition prove_axioms_id axioms : conjoin_axioms axioms -> conjoin_axioms axioms := fun x => x.

Require Import Coq.Logic.FunctionalExtensionality.

Goal {P:Prop | P}.
  eapply exist.
  instantiate (P:= (@Monoid ?[T] ?[m_zero] ?[m_plus])).
  apply (fun (H:conjoin_axioms [ax_pair "m_zero_left" _;
                                ax_pair "m_zero_right" _;
                                ax_pair "m_plus_assoc" _]) =>
           match H with conj pf1 (conj pf2 pf3) =>
                        Build_Monoid ?T ?m_zero ?m_plus pf1 pf2 pf3 end).
  instantiate (m_zero:=?[g_zero]).
  instantiate (m_plus:=?[g_plus]).
  instantiate (g_plus:=plus).

  set (my_plus := plus).

  pattern Nat.add in (value of my_plus).
  rewrite (functional_extensionality
             Nat.add tail_plus
             (fun n =>
                functional_extensionality _ _ (fun m => plus_tail_plus _ _)))
    in (value of my_plus).

  replace Nat.add with tail_plus in (value of my_plus).

  (*
  remember Nat.add as my_plus.

  rewrite (functional_extensionality
             Nat.add tail_plus
             (fun n =>
                functional_extensionality _ _ (fun m => plus_tail_plus _ _)))
    in Heqmy_plus.
  rewrite Heqmy_plus.
   *)


(*
Definition blah : conjoin_axioms
                    [ax_pair "m_zero_left"
                             (forall (x: (?[T]:Set)), (?[m_plus]: (?T -> ?T -> ?T) : Set) (?[m_zero]:?T) x = x)].
*)

Definition monoid_group_refinement : refinement.
  eapply Build_refinement. instantiate (rspec:=?[__Spec]).
  apply cons; [ | apply nil ]. intro __Model.
  eapply exist.
  instantiate (P:= (@Monoid ?[T] ?[m_zero] ?[m_plus])).

  apply (fun (H:conjoin_axioms [ax_pair "m_zero_left" _;
                                ax_pair "m_zero_right" _;
                                ax_pair "m_plus_assoc" _]) =>
           match H with conj pf1 (conj pf2 pf3) =>
                        Build_Monoid ?T ?m_zero ?m_plus pf1 pf2 pf3 end).

  instantiate (T:= ?[U]).
  (* rename T into U; instantiate (T:= ?U@{__Spec:=?__Spec; __Model:=__Model}). *)

  instantiate (U:= (?[U_L]:Set) -> ?[U_R]:Set).
  (*
  set (U_L := ?U_L); unfold U_L; move m_zero after U_L (* ; move m_plus after U_L *).
  set (U_R := ?U_R); unfold U_R; move m_zero after U_R (* ; move m_plus after U_R *).
  move U after U_R.
   *)
  (* rename m_zero into g_zero; *) instantiate (m_zero:=?[g_zero]).
  (* rename m_plus into g_plus; *) instantiate (m_plus:=?[g_plus]).
  (* clear U. *)
  set (g_double:= fun x => ?g_plus x x).

  eapply (add_axiom "g_inv_left");
    instantiate (tp:=(forall x, ?g_plus ((?[g_inv]) x) x = ?g_zero)).
  (*
  apply (add_axiom "g_inv_left" (forall x, ?g_plus ((?[g_inv]: (?U_L -> ?U_R) -> (?U_L -> ?U_R)) x) x = ?g_zero)).
   *)
  apply (add_axiom "g_inv_right" (forall x, ?g_plus x (?g_inv x) = ?g_zero)).
  unfold app.

  Show Proof.

  instantiate
    (__Spec:=
       Spec_ConsOp
         "U_L" Set Pred_Trivial
         (fun U_L _ =>
            Spec_ConsOp
              "U_R" Set Pred_Trivial
              (fun U_R _ =>
                 Spec_ConsOp
                   "g_zero" (U_L -> U_R) Pred_Trivial
                   (fun g_zero _ =>
                      Spec_ConsOp
                        "g_plus" ((U_L -> U_R) -> (U_L -> U_R) -> (U_L -> U_R)) Pred_Trivial
                        (fun g_plus _ =>
                           Spec_ConsOp
                             "g_inv" ((U_L -> U_R) -> (U_L -> U_R)) Pred_Trivial
                             (fun g_inv _ =>
                                Spec_Axioms
                                  [ax_pair "m_zero_left"
                                           (forall x, g_plus g_zero x = x);
                                    ax_pair "m_zero_right"
                                            (forall x, g_plus x g_zero = x);
                                    ax_pair "m_plus_assoc"
                                            (forall x y z,
                                               g_plus x (g_plus y z) =
                                               g_plus (g_plus x y) z);
                                    ax_pair "g_inv_left"
                                            (forall x,
                                               g_plus (g_inv x) x = g_zero);
                                    ax_pair "g_inv_right"
                                            (forall x,
                                               g_plus x (g_inv x) = g_zero)])))))).

  (*
  instantiate
    (__Spec:=
       Spec_ConsOp
         "U_L" Set Pred_Trivial
         (fun U_L _ =>
            Spec_ConsOp
              "U_R" Set Pred_Trivial
              (fun U_R _ =>
                 Spec_ConsOp
                   "g_zero" (U_L -> U_R) Pred_Trivial
                   (fun g_zero _ =>
                      Spec_ConsOp
                        "g_plus" ((U_L -> U_R) -> (U_L -> U_R) -> (U_L -> U_R)) Pred_Trivial
                        (fun g_plus _ =>
                           Spec_ConsOp
                             "g_inv" ((U_L -> U_R) -> (U_L -> U_R)) Pred_Trivial
                             (fun g_inv _ =>
                                Spec_Axioms
                                  ?[__axioms])))))).
   *)

  Show Proof.
  Show Existentials.
(*
  destruct __Model as [U_L__param __Model];
  destruct __Model as [U_L__proof __Model];
  destruct __Model as [U_R__param __Model];
  destruct __Model as [U_R__proof __Model];
  destruct __Model as [g_zero__param __Model];
  destruct __Model as [g_zero__proof __Model];
  destruct __Model as [g_plus__param __Model];
  destruct __Model as [g_plus__proof __Model];
  destruct __Model as [g_inv__param __Model];
  destruct __Model as [g_inv__proof __Model].
*)

  (* unfold __Model_var in U_L. instantiate (U_L:=U_L__param). *)

  (*
  apply __Model.
   *)
  (*
  apply (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 __Model)))))))))).
   *)

  apply (match __Model with
           | (existT
                _ _
                (existT
                   _ _
                   (existT
                      _ _
                      (existT
                         _ _
                         (existT
                            _ _
                            (existT
                               _ _
                               (existT
                                  _ _
                                  (existT
                                     _ _
                                     (existT
                                        _ _
                                        (existT
                                           _ _
                                           pf)))))))))) => pf end).

  instantiate (U_L :=
                 match __Model with
                   | existT _ x _ => x end). clear U_L.
  instantiate (U_R :=
                 match __Model with
                   | (existT _ _ (existT _ _ (existT _ x _))) => x end). clear U_R.
  instantiate
    (g_zero:=match __Model return (let (U_L,_) := __Model in U_L) ->
                                  (let (_,x1) := __Model in
                                   let (_,x2) := x1 in
                                   let (U_R,_) := x2 in U_R) with
               | (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ x _))))) => x end).
  unfold g_zero; clear g_zero.
  instantiate
    (g_plus:=match __Model return let T :=
                                      ((let (U_L,_) := __Model in U_L) ->
                                       (let (_,x1) := __Model in
                                        let (_,x2) := x1 in
                                        let (U_R,_) := x2 in U_R)) in T -> T -> T with
               | (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ x _))))))) => x end).
  instantiate
    (g_inv:=match __Model return let T :=
                                     ((let (U_L,_) := __Model in U_L) ->
                                      (let (_,x1) := __Model in
                                       let (_,x2) := x1 in
                                       let (U_R,_) := x2 in U_R)) in T -> T with
               | (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ _ (existT _ x _))))))))) => x end).
  
  destruct __Model as [U_L__param __Model];
  destruct __Model as [U_L__proof __Model];
  destruct __Model as [U_R__param __Model];
  destruct __Model as [U_R__proof __Model];
  destruct __Model as [g_zero__param __Model];
  destruct __Model as [g_zero__proof __Model];
  destruct __Model as [g_plus__param __Model];
  destruct __Model as [g_plus__proof __Model];
  destruct __Model as [g_inv__param __Model];
  destruct __Model as [g_inv__proof __Model].
  apply __Model.
Defined.

Print monoid_group_refinement.

Definition monoid_refinement : forall (M:spec_model2 ?M), @Monoid ?x1 ?x2 ?x3.

