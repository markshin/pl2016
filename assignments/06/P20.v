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


Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  intros.
  generalize dependent n.
  induction m. 
  intros. inversion H. simpl. reflexivity.
  intros. destruct n. simpl. reflexivity.
  simpl. 
  apply IHm.
  apply Sn_le_Sm__n_le_m.
  apply H.
Qed.
