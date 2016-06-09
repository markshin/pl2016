Require Export P02.



(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
    unfold deterministic.
  intros. generalize dependent y2.
  step_cases (induction H) Case; subst; intros.
-  inversion H0. reflexivity. 
  solve by inversion. 
-
  inversion H0. reflexivity.
  solve by inversion.
- inversion H0; subst. solve by inversion.
  solve by inversion.
  f_equal.   auto. 
- inversion H0. subst. f_equal.  auto. 
- inversion H0. reflexivity. inversion H1. 
- inversion H0. subst. reflexivity.
  assert (value t1). right. assumption.
  apply value_is_nf in H4. unfold normal_form, not in H4.
  inversion H2; subst. exfalso. apply H4. exists t1'0. assumption. 
- inversion H0; subst; try (solve by inversion).
  assert (value y2). right. assumption.
  apply value_is_nf in H1. unfold normal_form, not in H1.
  inversion H; subst. exfalso. apply H1. exists t1'0. assumption.
  apply IHstep in H2. rewrite H2. reflexivity.
- inversion H0; subst. reflexivity. solve by inversion.
- inversion H0; subst. reflexivity.
  assert (value t1). right. assumption. apply value_is_nf in H1.
  unfold normal_form, not in H1.
  inversion H2; subst. exfalso. apply H1. exists t1'0. assumption.
- inversion H0; subst; try (solve by inversion). 
  assert (value t0). right. assumption. apply value_is_nf in H1. 
  unfold normal_form, not in H1.
  inversion H; subst. exfalso. apply H1. exists t1'0. assumption. 
  rewrite (IHstep t1'0). reflexivity. assumption. 
Qed.
