Require Export D.



(** **** Problem #1 : 2 stars (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
 intros n m H.
 simpl.
 rewrite <- H.
 reflexivity.
Qed.

