Require Export P13.



(** **** Exercise: 1 star  *)
Lemma empty_colored_tree_CSearchTree: CSearchTree empty_colored_tree.
Proof.
  econstructor. instantiate (1:=0). instantiate (1:=0).
  econstructor. omega.
Qed.



