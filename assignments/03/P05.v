Require Export D.



(** There is a short solution to the next exercise.  If you find
    yourself getting tangled up, step back and try to look for a
    simpler way. *)
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  induction l1.
  simpl.
  induction l2. simpl. reflexivity.
  simpl. rewrite <- IHl2.
  reflexivity.
  simpl. rewrite -> IHl1.
  reflexivity.
Qed.

