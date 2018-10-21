Require Export P10.


Lemma de_morgan
  (P: Prop)
  (H: ~ (P \/ ~ P))
:
  (~P /\ ~~P).
Proof.
split; unfold not in *; intros.
-
apply H. auto.
-
apply H. auto.
Qed.

(** **** Problem #11 : 3 stars, advanced (not_exists_dist) *)
Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
intro P. 
unfold not. intros.
destruct (de_morgan P).
-
auto.
-
apply H1 in H0. auto.
Qed.
