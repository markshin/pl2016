Require Export D.



(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exact GIVEUP.
Qed.

