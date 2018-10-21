Require Export P11.



(** **** Problem #12 : 2 stars (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
intros n m N.
induction N; auto.
intros. simpl.
apply ev_SS. apply IHN. auto.
Qed.
