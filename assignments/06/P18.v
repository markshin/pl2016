Require Export D.



Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros.
  unfold lt.
  apply le_S. apply H.
Qed.
