Require Export P11.



(** **** Problem #3 : 3 stars (list_exercises) *)
(** More practice with lists. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  induction l; auto.
  simpl. rewrite IHl. auto.
Qed.
