Require Export P01.



(** **** Exercise: 1 star (not_a_permutation)  *)
(** Prove that [[1;1]] is not a permutation of [[1;2]].
    Hints are given as [Check] commands. *)

Check Permutation_cons_inv.
Check Permutation_length_1_inv.

Example not_a_permutation:
  ~ Permutation [1;1] [1;2].
Proof. unfold not. intros. apply Permutation_cons_inv in H.
apply Permutation_length_1_inv in H. inv H. Qed.

