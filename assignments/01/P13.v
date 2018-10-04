Require Export P12.



(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Lemma aux1
      l n
  :
    rev (snoc l n) = n :: (rev l).
Proof.
  induction l; auto.
  simpl. rewrite IHl. simpl. auto.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l; auto.
  simpl. rewrite aux1. rewrite IHl. auto.
Qed.

