Require Export D.



(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

(** 1 star (inversion_practice)  *)
Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion pf_evn.
    inversion pf_evn0.
Qed.
