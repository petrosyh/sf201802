Require Export P06.



(** **** Problem #7 : 2 stars (and_exercise) *)

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. 
induction n; induction m; auto.
-
intros.
inversion H.
-
intros.
inversion H.
Qed.


