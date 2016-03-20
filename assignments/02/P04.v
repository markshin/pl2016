Require Export D.



Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. 
  intros.
  induction n as [ | n'].
  simpl. reflexivity.
  simpl. rewrite -> IHn'.
  reflexivity.
Qed.

