Require Export D.



(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
    unfold not.
    unfold excluded_middle.
    intros.
    destruct H with (P := P x).
    apply H1. 
    apply ex_falso_quodlibet. 
    apply H0.
    exists x. apply H1.
Qed.
