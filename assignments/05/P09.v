Require Export D.



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  unfold not.
  intros.
  apply H in H1. apply H0 in H1. apply H1.
Qed.

