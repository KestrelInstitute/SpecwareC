(* Re-doing Examples/Specware-Overview/MergeSort.sw in SpecwareCoq *)

Load DivideAndConquer.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith_base.
Require Import Coq.Arith.Div2.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Relations.Relation_Operators.


(***
 *** Definitions of "sorted" and "permutation-of"
 ***)

(* A list is sorted iff it is empty, a singleton, or its first element is no
greater than its second and its tail is sorted. *)
Fixpoint sorted (l: list nat) : Prop :=
  match l with
    | [] => True
    | x::l' =>
      (match l' with
         | [] => True
         | y::_ => x <= y /\ sorted l'
       end)
  end.

(* Two lists are permutations of each other iff they have the same number of
occurrences of all elements. *)
Definition permOf (l1 l2: list nat) : Prop :=
  forall x, count_occ eq_nat_dec l1 x = count_occ eq_nat_dec l2 x.

Lemma permOf_refl l : permOf l l.
  intro x; reflexivity.
Qed.

Lemma permOf_sym l1 l2 : permOf l1 l2 -> permOf l2 l1.
  intros pof x; symmetry; apply (pof x).
Qed.

Lemma permOf_trans l1 l2 l3 :
  permOf l1 l2 -> permOf l2 l3 -> permOf l1 l3.
  intros pof12 pof23 x.
  rewrite (pof12 x). apply pof23.
Qed.

Lemma permOf_cons x l1 l2 :
  permOf l1 l2 -> permOf (x::l1) (x::l2).
  intros pof y. destruct (eq_nat_dec x y).
  rewrite (count_occ_cons_eq _ _ e); rewrite (count_occ_cons_eq _ _ e).
  f_equal; apply pof.
  rewrite (count_occ_cons_neq _ _ n); rewrite (count_occ_cons_neq _ _ n).
  apply pof.
Qed.

Lemma permOf_swap x y l : permOf (x::y::l) (y::x::l).
  intro z; unfold count_occ; fold (count_occ eq_nat_dec l).
  destruct (eq_nat_dec x z); destruct (eq_nat_dec y z); reflexivity.
Qed.

Lemma permOf_nil_cons x l : ~(permOf [] (x::l)).
  intro pof.
  assert (0 = count_occ eq_nat_dec (x::l) x); [ apply pof | ].
  rewrite (count_occ_cons_eq eq_nat_dec l eq_refl) in H.
  discriminate.
Qed.

Lemma permOf_app_cons l1 x l2 :
  permOf (l1 ++ x::l2) (x::l1 ++ l2).
  induction l1.
  intro y; reflexivity.
  intro y.
  unfold app; fold (app l1).
  unfold count_occ; fold (count_occ eq_nat_dec (l1++x::l2));
  fold (count_occ eq_nat_dec (l1++l2)).
  rewrite (IHl1 y).
  case_eq (eq_nat_dec a y); intros; case_eq (eq_nat_dec x y); intros.
  unfold count_occ; rewrite H0; reflexivity.
  unfold count_occ; rewrite H0; reflexivity.
  unfold count_occ; rewrite H0; reflexivity.
  unfold count_occ; rewrite H0; reflexivity.
Qed.


Lemma permOf_cons_in x l1 l2 :
  permOf (x::l1) l2 -> In x l2.
  intro pof.
  apply (proj2 (count_occ_In eq_nat_dec _ _)).
  rewrite <- pof.
  unfold count_occ; destruct (eq_nat_dec x x).
  apply lt_0_Sn.
  elimtype False; apply (n eq_refl).
Qed.

Lemma in_split_set x l :
  In x l -> { l1 : list nat & { l2 : list nat & l = l1 ++ x :: l2 } }.
  induction l; intros.
  elimtype False; apply H.
  destruct (eq_nat_dec a x).
  rewrite e. exists []; exists l; reflexivity.
  assert (In x l).
  destruct H; [ contradiction | assumption ].
  destruct (IHl H0) as [ l1 X ]; destruct X as [ l2 e ].
  exists (a::l1); exists l2. rewrite e. reflexivity.
Qed.

Lemma permOf_cons_inv x l1 l2 :
  permOf (x::l1) (x::l2) -> permOf l1 l2.
  intros pof y.
  assert (count_occ eq_nat_dec (x::l1) y =
          count_occ eq_nat_dec (x::l2) y); [ apply pof | ].
  unfold count_occ in H; fold (count_occ eq_nat_dec) in H.
  destruct (eq_nat_dec x y).
  injection H; intros; assumption.
  assumption.
Qed.

Lemma permOf_app l1 l1' l2 l2' :
  permOf l1 l1' -> permOf l2 l2' -> permOf (l1++l2) (l1'++l2').
  revert l1' l2 l2'; induction l1; intros.
  destruct l1'.
  assumption.
  elimtype False; apply (permOf_nil_cons n l1'); assumption.
  assert (In a l1').
  apply (permOf_cons_in _ l1); assumption.
  destruct (in_split_set a l1' H1) as [ l1'' X ]; destruct X as [ l2'' e ].
  rewrite e. rewrite <- app_assoc.
  rewrite <- app_comm_cons. rewrite <- app_comm_cons.
  apply (permOf_trans _ (a :: l1'' ++ l2'' ++ l2')).
  apply permOf_cons.
  rewrite app_assoc.
  apply IHl1.
  rewrite e in H.
  apply (permOf_cons_inv a).
  apply (permOf_trans _ _ _ H).
  apply permOf_app_cons.
  assumption.
  apply permOf_sym.
  apply permOf_app_cons.
Qed.


(***
 *** The high-level spec for sorting
 ***)

Spec Sorting.

Spec Variable sort : (list nat -> list nat).
Spec Axiom sort_correct :
  (forall l, sorted (sort l) /\ permOf l (sort l)).

Spec End Sorting.


(***
 *** The MergeSort0 spec, which instantiates all the elements of the
 *** DivideAndConquer_base spec for merge-sort.
 ***)

Spec MergeSort0.

(* Domain and range types *)
Spec Definition D : Type := (list nat).
Spec Definition R : Type := (list nat).

(* Input / output predicate *)
Spec Definition IO : (D -> R -> Prop) :=
  (fun lin lout => sorted lout /\ permOf lin lout).

(* The well-founded partial order on the inputs *)
Spec Definition smaller : (D -> D -> Prop) :=
  (fun l1 l2 => length l1 < length l2).

(* Proof that smaller is well-founded. Note that we make this a Definition
instead of a Theorem because DivideAndConquer_base requires well-foundedness to
be a subtype predicate and not an axiom. *)
Definition smaller_wf : (well_founded smaller) :=
  (well_founded_ltof _ _).


(***
 *** The base case, which is directly sorting a singleton list
 ***)

(* Test if a list is empty or a singleton; leb is the decision procedure for
deciding less-than-or-equal. *)
Spec Definition primitive : (D -> bool) :=
  (fun l => leb (length l) 1).

(* Sorting for an empty or singleton list is just the identity *)
Spec Definition direct_solve : (D -> R) := (fun l => l).


(***
 *** The decompose operation; requires list prefix and suffix
 ***)

(* Take the prefix of l of length <= n *)
Fixpoint list_prefix n l : list nat :=
  match n with
    | 0 => []
    | S n' =>
      match l with
        | [] => []
        | x::l' => x :: list_prefix n' l'
      end
  end.

(* Lemma: the length of list_prefix n l is no greater than n *)
Lemma list_prefix_len n l : length (list_prefix n l) <= n.
  revert l; induction n; intros.
  reflexivity.
  destruct l.
  apply le_0_n.
  apply le_n_S. apply IHn.
Qed.

(* Take the suffix of l, removing the first n elements, if they exist *)
Fixpoint list_suffix n l : list nat :=
  match n with
    | 0 => l
    | S n' =>
      match l with
        | [] => []
        | x::l' => list_suffix n' l'
      end
  end.

(* Lemma: the length of list_suffix n l is length l - n *)
Lemma list_suffix_len n l : length (list_suffix n l) = length l - n.
  revert l; induction n; intro l; destruct l; try reflexivity.
  unfold list_suffix; fold list_suffix.
  unfold length; fold (length l); fold (length (list_suffix n l)).
  apply IHn.
Qed.

(* Appending the prefix and the suffix yields the original list *)
Lemma list_prefix_suffix_eq n l : list_prefix n l ++ list_suffix n l = l.
  revert l; induction n; intro l; [ | destruct l ].
  reflexivity.
  reflexivity.
  unfold list_prefix; fold list_prefix.
  unfold list_suffix; fold list_suffix.
  unfold app; fold (app (list_prefix n l)).
  f_equal.
  apply IHn.
Qed.

(* The decompose operator splits a list into prefix and suffix *)
Spec Definition decompose : (D -> D * D) :=
  (fun l => (list_prefix (div2 (length l)) l,
             list_suffix (div2 (length l)) l)).

(* Proof that decompose yields smaller lists. As with smaller_wf, we make this a
Definition and not a Theorem because DivideAndConquer_base needs it as a proof
of a subtype predicate. *)
Definition decompose_smallerH l :
  primitive l = false ->
  smaller (fst (decompose l)) l /\ smaller (snd (decompose l)) l.
  intro H; unfold decompose, smaller, def, fst, snd.
  assert (1 < length l).
  apply leb_complete_conv. assumption.
  split.
  apply (le_lt_trans _ (div2 (length l))).
  apply list_prefix_len. apply lt_div2.
  transitivity 1; [ constructor | assumption ].
  rewrite list_suffix_len.
  apply lt_minus.
  apply lt_le_weak. apply lt_div2.
  transitivity 1; [ constructor | assumption ].
  destruct l.
  inversion H0.
  destruct l.
  inversion H0; inversion H2.
  apply lt_0_Sn.
Qed.

Definition decompose_smaller :
  (forall l,
     primitive l = false ->
     smaller (fst (decompose l)) l /\ smaller (snd (decompose l)) l) :=
  decompose_smallerH.


(***
 *** The compose operation, which requires list merge
 ***)

(* The length order on pairs of lists, which requires one of the two lists in
the pair to be smaller and the other to be the same list; this is called the
symmetric product of the length ordering. *)
Definition list_pair_smaller : list nat * list nat -> list nat * list nat -> Prop :=
  symprod _ _ smaller smaller.

(* Merge two lists *)
Function merge_lists (l_pair: list nat * list nat) {wf list_pair_smaller l_pair} : list nat :=
  let (l1,l2) := l_pair in
  match l1 with
    | [] => l2
    | x1::l1' =>
      match l2 with
        | [] => l1
        | x2::l2' =>
          if lt_dec x1 x2 then
            x1::merge_lists (l1',l2)
          else
            x2::merge_lists (l1,l2')
      end
  end.
intros. apply left_sym. apply le_n.
intros. apply right_sym. apply le_n.
apply wf_symprod; apply smaller_wf.
Defined.

(* Helper lemma: merge_lists applied to two cons lists yields a result whose
head is one of the two heads of the two lists. *)
Lemma merge_lists_cons_cons x1 l1 x2 l2 :
  {merge_lists (x1::l1, x2::l2) = x1::merge_lists (l1,x2::l2)} +
  {merge_lists (x1::l1, x2::l2) = x2::merge_lists (x1::l1,l2)}.
  assert (forall l_pair,
            l_pair = (x1::l1, x2::l2) ->
            {merge_lists l_pair = x1::merge_lists (l1,x2::l2)} +
            {merge_lists l_pair = x2::merge_lists (x1::l1,l2)}).
  intro l_pair; functional induction (merge_lists l_pair); intros; try discriminate.
  injection H; intros.
  rewrite H0; rewrite H1; rewrite H2; rewrite H3; left; reflexivity.
  injection H; intros.
  rewrite H0; rewrite H1; rewrite H2; rewrite H3; right; reflexivity.
  apply H; reflexivity.
Qed.

(* Helper lemma: merging two sorted lists is sorted *)
Lemma merge_lists_sorted l_pair :
  sorted (fst l_pair) -> sorted (snd l_pair) -> sorted (merge_lists l_pair).
  functional induction (merge_lists l_pair); unfold fst, snd; intros; try assumption.
  unfold sorted; fold sorted.
  destruct l1' as [ | x1' l1' ].
  split.
  apply lt_le_weak; assumption.
  apply IHl; [ constructor | assumption ].
  destruct (merge_lists_cons_cons x1' l1' x2 l2') as [ e_ml | e_ml ];
    rewrite e_ml; rewrite <- e_ml.
  split.
  destruct H; assumption.
  apply IHl; [ destruct H | ]; assumption.
  split.
  apply lt_le_weak; assumption.
  apply IHl; [ destruct H | ]; assumption.
  unfold sorted; fold sorted.
  destruct l2' as [ | x2' l2' ].
  split.
  destruct (le_or_lt x2 x1); [ assumption | contradiction ].
  assumption.
  destruct (merge_lists_cons_cons x1 l1' x2' l2') as [ e_ml | e_ml ];
    rewrite e_ml; rewrite <- e_ml.
  split.
  destruct (le_or_lt x2 x1); [ assumption | contradiction ].
  apply IHl; [ assumption | destruct H0; assumption ].
  split.
  destruct H0; assumption.
  apply IHl; [ assumption | destruct H0; assumption ].
Qed.

(* Helper lemma: merging lists yields a permutation of the original lists *)
Lemma merge_lists_permOf l_pair :
  permOf (fst l_pair ++ snd l_pair) (merge_lists l_pair).
  functional induction (merge_lists l_pair); unfold fst, snd.
  intro x; reflexivity.
  intro x; rewrite app_nil_r; reflexivity.
  apply permOf_cons; fold (app l1'); apply IHl.
  apply (permOf_trans _ (x2 :: (x1 :: l1') ++ l2')).
  apply permOf_app_cons.
  apply permOf_cons. apply IHl.
Qed.

Spec Definition compose : (R -> R -> R) := (fun l1 l2 => merge_lists (l1,l2)).


(***
 *** Correctness theorems for the base and step cases
 ***)

(* Theorem: direct_solve is correct for primitive problems *)
Spec Theorem direct_solve_correct :
  (forall l, primitive l = true -> IO l (direct_solve l)).
  unfold primitive, D, IO, direct_solve, def; intros.
  destruct l.
  (* Prove correctness for the empty list *)
  split.
  unfold sorted; trivial.
  unfold permOf; intros; reflexivity.

  destruct l.
  (* Prove correctness for singleton lists *)
  split.
  unfold sorted; trivial.
  unfold permOf; intros; reflexivity.

  (* Lists with more than 1 element contradict primitive l = true *)
  discriminate H.
Qed.


(* Theorem: if we solve the two decomposed problems then composing them is a
solution *)
Spec Theorem solve_soundness :
  (forall l lout1 lout2,
     IO (fst (decompose l)) lout1 ->
     IO (snd (decompose l)) lout2 ->
     IO l (compose lout1 lout2)).
  unfold D, R, decompose, compose, IO, def, fst, snd.
  intros l lout1 lout2 conj1 conj2; destruct conj1; destruct conj2.
  split.
  apply merge_lists_sorted; assumption.
  rewrite <- (list_prefix_suffix_eq (div2 (length l)) l).
  apply (permOf_trans _ (lout1 ++ lout2)).
  apply permOf_app; assumption.
  fold (fst (lout1,lout2)); fold (snd (lout1,lout2)).
  apply merge_lists_permOf.
Qed.

Spec End MergeSort0.


(***
 *** Now we make an interpretation from DivideAndConquer_base to MergeSort0
 ***)

Spec Interpretation DC_MergeSort0 : DivideAndConquer_base -> MergeSort0.
prove_simple_interp {{ }}.
apply (MergeSort0.smaller_wf (D__proof__param:=pf) (smaller__proof__param:=eq_refl)).
intros d H.
Check MergeSort0.decompose_smaller.
apply (MergeSort0.decompose_smaller
         (smaller__proof__param:=pf2) (primitive__proof__param:=pf3)
         (decompose__proof__param:=eq_refl)
         d H).
apply (MergeSort0.direct_solve_correct
         (D__param:=t) (D__proof__param:=pf) (R__param:=t0) (R__proof__param:=pf0)
         (IO__param:=t1) (IO__proof__param:=pf1)
         (primitive__param:=t3) (primitive__proof__param:=pf3)
         (direct_solve__proof__param:=pf4)
         d H).
apply (MergeSort0.solve_soundness
         (IO__proof__param:=pf1) (smaller__proof__param:=pf2)
         (decompose__proof__param:=pf5) (compose__proof__param:=pf6)
         _ _ _ H H0).
apply (MergeSort0.solve_soundness
         (IO__proof__param:=pf1) (smaller__proof__param:=pf2)
         (decompose__proof__param:=pf5) (compose__proof__param:=pf6)
         _ _ _ H H0).
Defined.
