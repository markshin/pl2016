Require Export D.



(** **** Exercise: 1 star (update_example)  *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.

  intros.
  unfold update. apply neq_id. intros contradiction. inversion contradiction.
Qed.

