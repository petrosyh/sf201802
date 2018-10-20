Require Export P07.



(** **** Problem #8 : 2 stars (not_implies_our_not) *)

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
intros. unfold not in H.
apply H in H0. inversion H0.
Qed.


