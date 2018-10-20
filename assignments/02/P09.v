Require Export P08.



(** **** Problem #9 : 2 stars (In_app_iff) *)

Lemma In_app_iff : forall A (l:list A) (l':list A) (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
intros. split.
-
revert l.
revert l'.
induction l.
+
simpl. auto.
+
simpl. intros.
inversion H.
*
repeat left. auto.
*
apply IHl in H0. inversion H0; auto.
-
intros. inversion H.
+
induction l.
*
inversion H0.
*
simpl in *. inversion H0; auto.
+
clear H.
induction l; auto. simpl. right.
auto.
Qed.

