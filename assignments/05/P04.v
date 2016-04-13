Require Export D.



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  inversion H. inversion H0.
  split. intros. apply H3 in H1. apply H1. apply H5.
  intros. apply H4 in H5. apply H2 in H5. apply H5.
Qed.

