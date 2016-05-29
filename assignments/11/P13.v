Require Export P12.



(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.

  intros.
  inversion H; subst.  
  induction n .
  exists st. split. apply multi_refl. assumption.  
  inversion IHn;subst.  inversion H2. inversion H4.
  exists (update x X (S n)).
  split. eapply multi_trans. apply H3. 
  apply par_body_n__Sn.
  assumption. split. auto. auto.     
    

Qed.

