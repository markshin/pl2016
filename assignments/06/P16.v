Require Export D.



Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  intros.
  induction b.
  rewrite plus_0_r.
  apply le_n.
  rewrite <- plus_n_Sm.
  apply le_S. apply IHb.
Qed.
