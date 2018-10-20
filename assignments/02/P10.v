Require Export P09.

Axiom functional_extensionality:
forall A B (f g : A -> B), (forall x, f x = g x) -> f = g.

Lemma list_assoc
  X (l1 l2 l3:list X)
:
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
induction l1; auto.
simpl. rewrite IHl1. auto.
Qed.

Lemma aux
  X (x:X) (l1 l2:list X)
:
  l1 ++ [x] ++ l2 = l1 ++ (x :: l2).
Proof.
induction l1; auto.
Qed.

(** **** Problem #10 : 4 stars (tr_rev_correct) *)
Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
intro. apply functional_extensionality. intros l.
induction l; auto. unfold tr_rev. simpl.
assert (forall X (l1 l2:list X), rev_append l1 l2 = rev l1 ++ l2).
{ clear. intro X. induction l1; auto.
intros. simpl. rewrite <- list_assoc. rewrite aux.
rewrite IHl1. auto. }
auto.
Qed.
