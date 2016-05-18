Require Export D.



(** **** Exercise: 2 stars (hoare_asgn_examples)  *)

Theorem assn_sub_ex1: 
  {{ (fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1)] }}
      X ::= APlus (AId X) (ANum 1)
  {{ fun st => st X <= 5 }}.
Proof.
  exact GIVEUP.
Qed.

