(***
 *** Utility functions and lemmas
 ***)

Require Export String.
Require Export List.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.EqdepFacts.
Require Export Coq.Logic.Eqdep_dec.


(* helper function for eliminating ors *)
Definition or_proj_r A B : ~A -> A \/ B -> B.
  intros not_A or; destruct or.
  elimtype False; apply not_A; assumption.
  assumption.
Qed.

(* helper function for eliminating ors *)
Definition or_proj_l A B : ~B -> A \/ B -> A.
  intros not_B or; destruct or.
  assumption.
  elimtype False; apply not_B; assumption.
Qed.



(*** useful list utility functions ***)

Lemma In_remove {A} eq_dec (x y : A) l : In x (remove eq_dec y l) -> In x l.
  induction l.
  intro in_pf; destruct in_pf.
  unfold remove; fold (remove eq_dec y); destruct (eq_dec y a); intro in_pf.
  right; apply IHl; assumption.
  destruct in_pf.
  left; assumption.
  right; apply IHl; assumption.
Qed.

Lemma remove_not_eq {A} eq_dec (x y : A) l :
  x <> y -> In x l -> In x (remove eq_dec y l).
  intro neq; induction l; intro in_pf.
  destruct in_pf.
  unfold remove; fold (remove eq_dec); destruct (eq_dec y a).
  destruct in_pf;
    [ elimtype False; apply neq; rewrite e; rewrite <- H; reflexivity
    | apply IHl; assumption ].
  destruct in_pf;
    [ left; assumption | right; apply IHl; assumption ].
Qed.


(*** UIP (and friends) for strings ***)

Module DecidableSetString.
  Definition U := string.
  Definition eq_dec : forall x y:U, {x=y} + {x<>y} := string_dec.
End DecidableSetString.

Module EqDepString := DecidableEqDep (DecidableSetString).

Definition UIP_refl_string (str : string) (e : str=str) : e = eq_refl :=
  EqDepString.UIP_refl str e.

Lemma string_dec_true str : string_dec str str = left eq_refl.
  destruct (string_dec str str).
  rewrite (UIP_refl_string _ e); reflexivity.
  elimtype False; apply n; reflexivity.
Qed.


(*** UIP and friends for field types ***)

Section UIP_fields.

  Variable F : Set.
  Variable F_dec : forall (fld1 fld2 : F), {fld1=fld2} + {fld1<>fld2}.

  Lemma F_dec_true fld : F_dec fld fld = left eq_refl.
    destruct (F_dec fld fld).
    rewrite (UIP_dec F_dec e eq_refl); reflexivity.
    elimtype False; apply n; reflexivity.
  Qed.

  Definition UIP_flds { flds1 flds2 : list F } (p1 p2 : flds1 = flds2) : p1 = p2 :=
    UIP_dec (list_eq_dec F_dec) p1 p2.

  Definition UIP_refl_flds { flds } (p : flds = flds) : p = eq_refl :=
    UIP_flds p eq_refl.

  Definition eq_dep_eq_flds P {flds} {x y : P flds}
             (ed : eq_dep _ P flds x flds y) : x = y :=
    eq_dep_eq_dec (list_eq_dec F_dec) ed.

  (* inj_pair2 for lists of strings *)
  Definition inj_pair2_flds {flds : list F} {A a b}
             (e : existT A flds a = existT A flds b) : a = b :=
    eq_dep_eq__inj_pair2 _ (eq_dep_eq_flds) _ _ _ _ e.


  (*** helpers for proving eq_dep goals ***)

  Lemma eq_dep_fst {A B p x q y} : eq_dep A B p x q y -> p = q.
    intro e; destruct e; reflexivity.
  Qed.

  Lemma eq_dep_commute A B (a1 a2 : A) (b1 : B a1) (b2 : B a2)
        C (f : forall x (y : B x), C x y) :
    eq_dep _ _ a1 b1 a2 b2 ->
    eq_dep _ (fun tup => C (projT1 tup) (projT2 tup))
           (existT B a1 b1) (f a1 b1)
           (existT B a2 b2) (f a2 b2).
    intro e; induction e.
    apply eq_dep_intro.
  Qed.

  Lemma eq_dep_ctx A B (a1 a2 : A) (b1 : B a1) (b2 : B a2)
        A' (f : A -> A')
        B' (g : forall x, B x -> B' (f x)) :
    eq_dep _ _ a1 b1 a2 b2 ->
    eq_dep _ _ (f a1) (g a1 b1) (f a2) (g a2 b2).
    intro e; induction e.
    apply eq_dep_intro.
  Qed.

  Lemma eq_dep_flds_fun U B (a1 a2 : list F)
        (b1 : U -> B a1) (b2 : U -> B a2) (e : a1 = a2) :
    (forall u, eq_dep _ B a1 (b1 u) a2 (b2 u)) ->
    eq_dep _ (fun a => U -> B a) a1 b1 a2 b2.
    revert b1 b2; rewrite e; intros.
    rewrite (functional_extensionality_dep
               _ _
               (fun u' => eq_dep_eq_flds _ (H u'))).
    apply eq_dep_intro.
  Qed.

End UIP_fields.
