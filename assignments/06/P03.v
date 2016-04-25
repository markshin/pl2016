Require Export D.



(** 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   intros.
   induction m.
   simpl. apply b_0.
   simpl. apply b_sum with (n := n) (m := m*n).
   apply H. apply IHm.
Qed.
