Require Export D.



(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a SKIP after a command results in an equivalent
    program *)

Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof. 
  exact GIVEUP.
Qed.

