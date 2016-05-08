Require Export D.



(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof. 
    unfold cequiv.
  intros. split; intros.
  inversion H1; subst.
  apply E_Seq with (st' := st'0). apply H.  assumption.  apply H0. assumption. 
  inversion H1; subst.
  apply E_Seq with (st' := st'0).
  apply H. assumption. apply H0; assumption. 
Qed.

