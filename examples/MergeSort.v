
Load Sort.


Spec MergeSort1 := transform Sorting_dnc.
  begin_refinement.
  instantiate (primitive__field :=
                 (fun (l:list nat) => Nat.leb (length l) 1)).
  instantiate (decomposeL__field:=
                 (fun l => firstn (Nat.div2 (length l)) l)).
  instantiate (decomposeR__field:=
                 (fun l => skipn (Nat.div2 (length l)) l)).
  instantiate (smaller__field:=
                 (fun l1 l2 => length l1 <= length l2)).

  intros d rL rR H1 H2.
  rewrite <- (firstn_skipn (Nat.div2 (Datatypes.length d)) d).
  revert H1 H2.
  simpl.
  generalize (firstn (Nat.div2 (Datatypes.length d)) d).
  generalize (skipn (Nat.div2 (Datatypes.length d)) d).
  clear d.
  revert rL rR.

  instantiate (compose__field:=?[merge]).
  instantiate (a:=?[merge_correct]).

  (* shelve. *)

  (*
  intro d; induction d; intros.
  rewrite Compare_dec.leb_iff_conv in H.
  inversion H.
  destruct d.
  rewrite Compare_dec.leb_iff_conv in H.
  elimtype False; apply (Lt.lt_irrefl _ H).
  unfold length; repeat (fold (@length nat)).
  unfold Nat.div2; fold (Nat.div2).
  unfold skipn; fold (@skipn nat).
  apply le_n_S.
  *)

  end_refinement.
Defined.

Print MergeSort1.
