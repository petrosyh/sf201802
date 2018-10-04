Require Export P13.



Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  induction l; auto.
  intros. simpl. rewrite IHl. auto.
Qed.
