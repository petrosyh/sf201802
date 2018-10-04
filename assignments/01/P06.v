Require Export P05.




Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n.
  - intros. auto.
  - intros.
    rewrite plus_Sn_m.
    rewrite <- plus_n_Sm. rewrite (IHn m). auto.
Qed.
