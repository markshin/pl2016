Require Export D.



(** **** Problem #19 : 2 stars (beq_nat_true)  *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction  n. intros.  destruct  m.
  reflexivity.
  inversion H. intros.
  destruct m.
  inversion H.
  simpl in H.
  apply f_equal.
  apply IHn.
  apply H.
Qed.

