Require Export P01.



(** **** Problem #2: 2 stars (filter_even_gt7) *)
(** Use filter (instead of Fixpoint) to write a Coq function
    filter_even_gt7 that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than 7. *)
SearchAbout nat.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun b => (andb (evenb b) (negb (Nat.leb b 7)))) l. 

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. auto. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. auto. Qed.

