Require Export D.



(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  unfold stuck.
  intros. unfold not.
  Print tm.
  exists (tsucc ttrue).
  split.
  Print step_normal_form.
    unfold normal_form. unfold not.
    intros. inversion H; subst. inversion H0. subst. 
    inversion H2.
    intros.
    inversion H;subst. inversion H0. inversion H0; subst.
    inversion H2. 
Qed.

