Require Export D.


Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
      intros.
  induction H.
  apply le_n. apply le_S. apply IHle.
Qed.



Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  intros n.
  induction n.
  intros. induction m. apply le_n.
  apply le_S. apply IHm. simpl. reflexivity.
  intros. induction m. inversion H.
  apply n_le_m__Sn_le_Sm. apply IHn.
  inversion H. reflexivity.
Qed.
