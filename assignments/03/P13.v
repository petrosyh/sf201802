Require Export P12.



(** **** Exercise: 3 stars (insert_SearchTree)  *)

Check SearchTree'_range.
Check SearchTree'_expand.

Theorem insert_SearchTree:
  forall k v t,
   SearchTree t -> SearchTree (insert k v t).
Proof.
  intros until 1. inv H.
  assert (0<=k) by omega.
  bdestruct (k<? hi).
  - econstructor. eapply insert_SearchTree'_noexpand; eauto.
  - econstructor.
    (* inv H0. *)
    remember 0 as lo. clear Heqlo.
    clear H. revert H1. revert k. revert v. (* revert H0. revert hi. revert lo. *)
    induction H0.
    + instantiate (1 := S k).
      econstructor; econstructor; omega.
    + intros. simpl. bdestruct (k<?k0).
      * bdestruct (k0<?k); try omega.
        econstructor; eauto.
      * eapply SearchTree'_range in H0_0. omega.
Qed.
