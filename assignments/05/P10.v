Require Export D.



(** 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
    intros.
    unfold not.
    intros.
    destruct H.
    apply H0 in H.
    apply H.
Qed.

