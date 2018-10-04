Require Export P06.



Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n as [| n']; auto.
  intros. simpl. apply eq_S. auto.
Qed.

