Require Export D.

Theorem beq_nat_true : forall k1 k2, beq_nat k1 k2 = true -> k1 = k2.
Proof.
    intros k1.
    induction k1.
    intros. destruct k2.
    reflexivity. inversion H.
    intros. destruct k2. inversion H.
    apply f_equal. simpl in H. apply IHk1. apply H.
Qed.

(** **** Problem #24 : 2 stars (override_same)  
    Hint: use the lemma [beq_nat_true]. *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k2) eqn:l. rewrite <- H.
  apply f_equal.
  apply beq_nat_true in l. apply l.
  reflexivity.
Qed.

