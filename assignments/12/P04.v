Require Export P03.



(** **** Exercise: 1 star, optional (succ_hastype_nat__hastype_nat)  *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.  
Proof.
  exact GIVEUP.
Qed.

