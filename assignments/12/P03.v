Require Export P02.



(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  exact GIVEUP.
Qed.

