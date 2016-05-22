Require Export P11.



(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
    unfold is_wp.
  split.
  apply hoare_asgn.
  unfold assert_implies.
  unfold hoare_triple. 
  intros. 
  assert (Q (update st X (aeval st a))).
  eapply H. constructor. reflexivity. apply H0.
  apply H1.
Qed.

