Require Export D.



(** 2 star (ev__even)  *)
Theorem ev__even: forall n : nat,
  ev n -> even n.
Proof.
  intros.
  induction H.
  unfold even. simpl. reflexivity.
  unfold even. unfold even in IHev.
  simpl. apply IHev.
Qed.
