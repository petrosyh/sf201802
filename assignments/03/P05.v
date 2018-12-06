Require Export P04.



(** **** Exercise: 4 stars (l_insert_sorted)  *)
(** This one is a bit tricky.  However, there just a single induction
   right at the beginning, and you do _not_ need to use [l_insert_perm]
   or [sort_perm]. *)

Lemma l_insert_sorted:
  forall a l, sorted l -> sorted (l_insert a l).
Proof.
  induction 1.
  - simpl. econstructor.
  - simpl. bdestruct (a<=?x); econstructor; auto; try econstructor.
    omega.
  - simpl in *.
    bdestruct (a<=?x).
    + do 2 (eapply sorted_cons; eauto).
    + bdestruct (a<=?y).
      * econstructor; try omega. auto.
      * econstructor; try omega. auto.
Qed.


