Require Export D.

Theorem gorgeous_sum : forall n m,
      gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
      intros.
  induction H. simpl. apply H0.
  apply g_plus3. apply IHgorgeous.
    apply g_plus5. apply IHgorgeous.
Qed.

(** 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 intros.
 induction H.
 apply g_0.
 apply g_plus3. apply g_0.
 apply g_plus5. apply g_0.
 apply gorgeous_sum.
 apply IHbeautiful1. apply IHbeautiful2.
Qed.

