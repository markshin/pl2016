Require Export D.



(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a SKIP after a command results in an equivalent
    program *)

Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof. 
    intros c st st'.
  split; intros. 
  inversion H. subst.  inversion H5. subst.
  apply H2. 

  apply E_Seq with st'. apply H. apply E_Skip.
Qed.

