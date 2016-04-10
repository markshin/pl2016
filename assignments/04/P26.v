Require Export D.



(** **** Problem #25 : 3 stars, advanced (filter_exercise)  *)
(** This one is a bit challenging.  Pay attention to the form of your IH. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros.
  generalize dependent test.
  generalize dependent x.
  generalize dependent lf.
  induction l.
  simpl. intros. inversion H.
  simpl. intros. destruct (test x) eqn:t.
  inversion H. rewrite <- H1. apply t.
  apply IHl in H. apply H.
Qed.

