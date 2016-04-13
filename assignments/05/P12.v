Require Export D.

Lemma ex_falso_quodlibet : forall P : Prop, False -> P.
Proof.
    intros.
    inversion H.
Qed.




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
    intros.
    unfold not in H.
    generalize dependent m.
    induction n.
    intros.  destruct m. simpl.
    
    apply ex_falso_quodlibet.
    apply H. reflexivity.
    simpl. reflexivity.
    intros. destruct m. simpl. reflexivity.
    simpl. apply IHn. 
    intros. apply H.
    apply f_equal. apply H0.
Qed.

