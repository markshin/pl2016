Require Export P06.



(** **** Exercise: 2 stars (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
  intros. 
  induction H0; subst.
  constructor. 
  apply multi_step with (P t1 y).
  apply ST_Plus2. assumption. assumption.
  assumption. 
Qed.

