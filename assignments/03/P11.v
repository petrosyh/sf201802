Require Export P10.



(** **** Exercise: 3 stars (insert_relate)  *)

Check t_update_shadow.
Check t_update_permute.

Lemma t_update_combine_r:
  forall k V (a b: total_map V) v0 k0 (HLT:k < k0),
  t_update (combine k a b) k0 v0 = combine k a (t_update b k0 v0).
Proof.
  intros.
  unfold t_update, combine, t_empty.
  extensionality x.
  bdestruct (k0=?x); subst.
  - bdestruct (x<?k); auto. omega.
  - bdestruct (x<?k); auto.
Qed.

Theorem insert_relate:
 forall k v t cts,
    Abs t cts ->
    Abs (insert k v t) (t_update cts k v).
Proof.
  intros k v t cts H. revert k. revert v.
  induction H.
  - intros.
    evar (m: total_map V).
    replace (t_update (t_empty default) k v) with m; subst m.
    { unfold insert. repeat econstructor. }
    unfold  t_update, combine, t_empty.
    extensionality x.
    bdestruct (k=?x); auto.
    bdestruct (x<?k); auto.
  - intros.
    simpl. bdestruct (k0<?k).
    + rewrite t_update_permute; try omega.
      rewrite t_update_combine_l; auto.
      econstructor; auto.
    + apply le_lt_or_eq in H1.
      inv H1; cycle 1.
      * bdestruct (k0<?k0).
        { omega. }
        rewrite t_update_shadow. econstructor; eauto.
      * bdestruct (k<?k0); cycle 1.
        { omega. }
        rewrite t_update_permute; cycle 1.
        { omega. }
        rewrite t_update_combine_r; auto.
        econstructor; auto.
Qed.
