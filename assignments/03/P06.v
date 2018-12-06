Require Export P05.



(** **** Exercise: 2 stars (sort_sorted)  *)
(** This one is easy.   *)

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  induction l.
  - simpl. econstructor.
  - simpl. apply l_insert_sorted. auto.
Qed.



