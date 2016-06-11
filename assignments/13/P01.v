Require Export D.



(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Lemma K:
  forall T1 T2, ~ T1 = TArrow T1 T2.
Proof.
  unfold not.
  intros. generalize dependent T2. 
  induction T1; intros; 
  inversion H.
  apply IHT1_1 in H1. assumption. 
Qed.


Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  intros Hc.
  destruct Hc.
  destruct H. 
 
  inversion H; subst. clear H.
  inversion H5; subst. clear H5.
  inversion H2; subst. clear H2. 
  inversion H4; subst. clear H4.
  
  rewrite extend_eq in H1.
  rewrite extend_eq in H2. rewrite H1 in H2. 
  inversion H2. 
   symmetry in H0. 
  apply K in H0. 
  assumption.


Qed.

