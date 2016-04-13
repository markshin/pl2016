Require Export D.



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
    intros.
    unfold not.
    generalize dependent m.
    induction n.
    intros. destruct m. inversion H.
    inversion H0.
    intros. destruct m.
    inversion H0. simpl in H.
    apply IHn in H.
    apply H.
    assert (L : forall n m, S n = S m -> n = m).
    intros. inversion H1. reflexivity.
    apply L. apply H0.
Qed.

