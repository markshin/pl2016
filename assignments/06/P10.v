Require Export D.



(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  exact GIVEUP.
Qed.

Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
  exact GIVEUP.
Qed.

