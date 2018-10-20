Require Export D.



(** **** Problem #1: 1 star (hd_error_poly) *)
(** The hd function returns the first element (the "head") of
    the list, or None if the list has no first element.
*)

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | hd :: tl => Some hd
  end.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. auto. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. auto. Qed.
Example test_hd_error3 : @hd_error nat [] = None.
Proof. auto. Qed.

