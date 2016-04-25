Require Export D.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
      intros.
  induction H0.
  apply H.
    apply le_S. apply IHle. apply H.


Qed.

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


Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  intros.
  apply ble_nat_true in H. apply ble_nat_true in H0.
  apply le_ble_nat. generalize dependent H0.
  generalize dependent H.
  apply le_trans.
Qed.
