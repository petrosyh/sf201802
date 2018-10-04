Require Export P14.



Lemma aux2
      l1 l2 n
  :
    snoc (l1 ++ l2) n = l1 ++ snoc (l2) n.
Proof.
  induction l1; auto.
  simpl. rewrite IHl1. auto.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  induction l1; simpl.
  - intros. rewrite app_nil_end. auto.
  - intros. rewrite IHl1. rewrite aux2.
    auto.
Qed.
