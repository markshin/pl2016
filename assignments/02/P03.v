Require Export D.

Theorem plus_0_r: forall n :nat, n + 0 = n.
Proof.
    intros n. induction n as [ |n'].
    reflexivity.
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m :nat, S (n + m) = n + (S m).
Proof. 
    intros.
    induction n as [ | n'].
    simpl. reflexivity.
    simpl. rewrite IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. 
  intros.
  induction n as [ | n'].
  simpl. rewrite -> plus_0_r.
  reflexivity.
  simpl. rewrite <- plus_n_Sm.
  rewrite <- IHn'.
  reflexivity.
Qed.

