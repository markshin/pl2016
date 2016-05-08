Require Export D.



(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros. generalize dependent st. 
  induction c; intros.
  exists st. constructor.
  simpl in *. exists (update st i (aeval st a)). constructor. reflexivity.
  
  simpl in *. apply andb_true_iff in NOWHL. inversion NOWHL.
  apply IHc1 with st in H. inversion H. apply IHc2 with x in H0. inversion H0 as [st2].
  exists st2.  apply E_Seq with x. apply H1. apply H2. 

  simpl in *. apply andb_true_iff in NOWHL. inversion NOWHL.
  apply IHc1 with st in H. inversion H.
  apply IHc2 with st in H0. inversion H0.
  destruct (beval st b) eqn:B. exists x. apply E_IfTrue. apply B.
  apply H1. exists x0.  apply E_IfFalse. apply B. apply H2. 
  inversion NOWHL.  



Qed.

