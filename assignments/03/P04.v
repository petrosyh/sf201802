Require Export P03.



(** **** Exercise: 3 stars (sort_perm)  *)
(** Now prove that sort is a permutation. *)

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  induction l.
  - simpl. econstructor.
  - simpl. apply Permutation_sym. eapply Permutation_trans.
    { instantiate (1:= a::(sort l)).
      apply Permutation_sym. apply l_insert_perm. }
    apply perm_skip. apply Permutation_sym. auto. Qed.


