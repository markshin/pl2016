Require Export D.

Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. destruct (eq_id_dec x1 x2). subst. reflexivity.
  reflexivity.
  Qed.

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
      intros. unfold aequiv in H.
  split; intros. 
  inversion H0; subst. 
  
  
  assert (st' = (update st' X (st' X))).
  apply functional_extensionality. intros. rewrite update_same; reflexivity. 

   
  rewrite H1 at 2. constructor. rewrite <- H. simpl. reflexivity. 
  inversion H0; subst.
  assert (st = update st X (aeval st e)).
  rewrite <- H. 
  apply functional_extensionality. intros. rewrite update_same. reflexivity.
  simpl. reflexivity.
  rewrite <- H1. constructor.    

Qed.

