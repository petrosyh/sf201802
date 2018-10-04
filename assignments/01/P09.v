Require Export P08.



(** **** Problem : 3 stars (mult_comm) *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  induction n; auto.
  simpl. intros. rewrite (IHn m p).
  rewrite plus_assoc. auto.
Qed.


