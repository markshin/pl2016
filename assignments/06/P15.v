Require Export D.



Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros.
  generalize dependent n.
  induction m.
  intros. inversion H. apply le_n.
  inversion H2. 
  intros. inversion H. apply le_n.  
apply le_S. apply IHm. apply H2.
Qed.
