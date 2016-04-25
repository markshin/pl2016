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

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
      intros.
  induction H0.
  apply H.
  apply le_S. apply IHle. apply H.
Qed.

Lemma K : forall n1 n2, n1 <= S (n1 + n2).
Proof.
    intros.
    apply le_S.
    apply le_plus_l.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
      n <= m -> S n <= S m.
Proof. 
      intros.
  induction H.
  apply le_n. apply le_S. apply IHle.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt. 
 intros. inversion H. split.
 apply n_le_m__Sn_le_Sm.
 apply le_plus_l.
 apply n_le_m__Sn_le_Sm. rewrite plus_comm.
 apply le_plus_l.

split.
apply n_le_m__Sn_le_Sm.
apply le_trans with (m := n1) ( n := (S (n1+n2))) ( o := m0).
apply K. apply H0.
apply n_le_m__Sn_le_Sm.
apply le_trans with (m := n2) (n := (S (n1 + n2))) ( o := m0).
rewrite plus_comm. apply K. apply H0.
Qed.




