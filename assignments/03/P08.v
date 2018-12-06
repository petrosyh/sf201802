Require Export P07.



(** **** Exercise: 3 stars (sorted'_sorted)  *)
Lemma sorted'_sorted: forall al, sorted' al -> sorted al.
Proof.
  induction al.
  - intros. econstructor.
  - intros.
    assert (sorted' al).
    { unfold sorted' in *.
      intros. specialize (H (S i) (S j)). simpl in H.
      apply H; omega. }
    destruct al.
    { econstructor. }
    apply sorted_cons; eauto.
    unfold sorted' in H.
    specialize (H 0 1). simpl in *. apply H. omega.
Qed.



