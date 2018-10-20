Require Export P02.



(** **** Problem #3 : 3 stars (map_rev) *)

Lemma map_rev_aux
  X Y (f:X -> Y) (x:X) (l:list X)
:
  map f (l ++ [x]) = map f l ++ [f x].
Proof.
induction l; simpl; auto.
rewrite IHl. auto. Qed.

(* Show that map and rev commute. You may need to define an auxiliary lemma. *)
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros.
induction l.
- 
simpl. auto.
- 
simpl. rewrite <- IHl.
rewrite map_rev_aux. auto.
Qed.

