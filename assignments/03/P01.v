Require Export D.



(** **** Exercise: 3 stars (permut_example)  *)
(** Use the permutation rules in the library (see the [Search],
    above) to prove the following theorem.  These [Check] commands
   are a hint about what lemmas you'll need. *)

Check perm_skip.
Check Permutation_refl.
Check Permutation_app_comm.
Check app_assoc.

Example permut_example: forall (a b: list nat),
  Permutation (5::6::a++b) ((5::b)++(6::a++[])).
Proof.
  intros. simpl.
  apply perm_skip. rewrite app_nil_r.
  assert (6::a++b = [6]++a++b).
  { simpl. auto. }
  rewrite H. rewrite app_assoc.
  eapply Permutation_app_comm with (l:= 6::a).
Qed.


