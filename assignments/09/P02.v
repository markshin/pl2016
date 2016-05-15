Require Export P01.

Theorem WHILE_false
     : forall (b : bexp) (c : com),
       bequiv b BFalse -> cequiv (WHILE b DO c END) SKIP.
Proof.
    intros b c Hb.
    split; intros H.
    inversion H; subst.
apply E_Skip.
rewrite Hb in H2. inversion H2. 
inversion H; subst. 
apply E_WhileEnd.
rewrite Hb. 
reflexivity.
         
  
Qed.


(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** Complete the [WHILE] case of the following proof. *)

Theorem fold_constants_com_sound : 
  ctrans_sound fold_constants_com.
Proof. 
  unfold ctrans_sound. intros c. 
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";;". 
    (***
     Note how we use the tactic [eauto].
     ***)
   destruct c1; destruct c2; try (apply CSeq_congruence; assumption)
   ; eauto using skip_left, skip_right.
  Case "IFB". 
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Heqb;
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
      assert (bequiv b (fold_constants_bexp b)).
  apply fold_constants_bexp_sound.
  destruct (fold_constants_bexp b) eqn:Heqb; try (apply WHILE_true; assumption); try (apply CWhile_congruence; assumption).
  apply trans_cequiv with (WHILE BFalse DO c END).
  apply CWhile_congruence. assumption. apply refl_cequiv.
  apply WHILE_false. apply refl_bequiv.
Qed.

