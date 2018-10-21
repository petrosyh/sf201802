Require Export P12.



(** **** Problem #13 : 3 stars (le_exercises) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof. 
intros m n o H H1.
revert H. revert m.
induction H1; auto.
intros. apply le_S.
apply IHle. auto.
Qed.

