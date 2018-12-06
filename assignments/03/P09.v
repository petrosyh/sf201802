Require Export P08.



(** **** Exercise: 2 stars (check_example_map)  *)
(** Prove that [example_map] is the right one.
     You will probably need the [bdestruct] tactic, and [omega].
     For the beginning part of the proof, you can get hints from
     SearchTree chapter *)
Lemma check_example_map:
  forall v2 v4 v5, Abs (example_tree v2 v4 v5) (example_map v2 v4 v5).
Proof.
  intros.
  unfold example_tree.
  evar (m: total_map V).
  replace (example_map v2 v4 v5) with m; subst m.
  repeat constructor.
  extensionality x.
  unfold example_map, t_update, combine, t_empty.
  bdestruct (4=?x).
  - subst. simpl. auto.
  - bdestruct (x<?4).
    + bdestruct (2=?x).
      { subst; auto. }
      bdestruct (x<?2).
      { bdestruct (5=?x).
        - subst. omega.
        - auto. }
      bdestruct (5=?x).
      { subst; omega. }
      auto.
    + bdestruct (5=?x); auto.
      bdestruct (x<?5).
      { omega. }
      bdestruct (2=?x).
      { omega. }
      auto.
Qed.


