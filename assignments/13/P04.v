Require Export P03.



Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
 unfold not, stuck. unfold not.
 intros.
    destruct H1. 
    unfold normal_form in H1.
    unfold not in H1. 
    induction H0.
    apply progress in H.
    inversion H. apply H2 in H0. auto.
    apply H1 in H0. auto. 
    eapply preservation in H. 
    apply IHmulti in H. auto. 
    apply H1. apply H2. apply H0.   



Qed.

