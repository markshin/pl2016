Require Export D.



(** 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    intros.
    simpl.
    apply b_sum with (n := n) (m := n + 0).
    apply H.
    rewrite -> plus_0_r.
    apply H.
Qed.
