Require Export P11.



(** **** Exercise: 2 stars (insert_SearchTree'_noexpand)  *)
Lemma insert_SearchTree'_noexpand:
  forall t a b k v (HST':SearchTree' a t b)
         (HLT:a <= k < b),
    SearchTree' a (insert k v t) b.
Proof.
  intros t a b k v H. revert k. revert v.
  induction H.
  - intros. simpl. econstructor; eauto.
    + econstructor. omega.
    + econstructor. omega.
  - intros. simpl.
    bdestruct (k0<?k).
    + econstructor.
      { eapply IHSearchTree'1. omega. }
      { auto. }
    + bdestruct (k<?k0).
      * econstructor; auto. eapply IHSearchTree'2; auto. omega.
      * assert (k = k0) by omega. subst.
        econstructor; auto.
Qed.


