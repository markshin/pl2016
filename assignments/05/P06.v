Require Export D.



(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros. destruct b.
  left. reflexivity.
  destruct c. right. reflexivity.
  inversion H.
Qed.

