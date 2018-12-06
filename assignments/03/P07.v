Require Export P06.



(** **** Exercise: 4 stars (sorted_sorted')  *)
Lemma sorted_sorted': forall al, sorted al -> sorted' al.
Proof.
  induction 1.
  - unfold sorted'. intros. inv H. inv H1.
  - unfold sorted'. intros. inv H. inv H1. inv H0. inv H2.
  - unfold sorted' in *. intros.
    destruct (le_lt_dec 1 i).
    + inv l0.
      { simpl. destruct j.
        - inv H1. inv H2.
        - simpl in *.
          specialize (IHsorted 0). simpl in *. apply IHsorted. omega. }
      { simpl in *.
        destruct j.
        - inv H1. inv H3.
        - apply IHsorted. omega. }
    + inv l0; cycle 1.
      { inv H3. }
      destruct j.
      { inv H1. inv H2. }
      simpl.
      assert (y <= match j with
                  | 0 => y
                  | S m => nth m l 0
                  end).
      { destruct j; try omega. specialize (IHsorted 0 (S j)). simpl in IHsorted.
        apply IHsorted. simpl in *. inv H1. clear H2. omega. }
      eapply Nat.le_trans; eauto. Qed.

