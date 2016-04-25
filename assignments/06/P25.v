Require Export D.



(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   intros.
   split.
   intros.
   destruct H.
   destruct proof.
   left. exists witness. apply H.
   right. exists witness. apply H.
   intros.
   destruct H. destruct H.
   exists witness. left. apply proof.
   destruct H. exists witness. right. apply proof. 
Qed.
