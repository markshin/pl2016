Require Export P03.



Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
 unfold btrans_sound.
  induction b.  simpl. apply refl_bequiv.
  simpl. apply refl_bequiv.

  unfold bequiv. intros. simpl.
  remember (optimize_0plus_aexp a) as a' eqn:Heqa'. remember (optimize_0plus_aexp a0) as a0' eqn:Heqa0'.
  replace (aeval st a) with (aeval st a') by (subst a'; rewrite <- optimize_0plus_aexp_sound; reflexivity). 
  replace (aeval st a0) with (aeval st a0') by (subst a0'; rewrite <- optimize_0plus_aexp_sound; reflexivity).
  reflexivity.

  unfold bequiv. intros. simpl.
  remember (optimize_0plus_aexp a) as a' eqn:Heqa'. remember (optimize_0plus_aexp a0) as a0' eqn:Heqa0'.
  replace (aeval st a) with (aeval st a') by (subst a'; rewrite <- optimize_0plus_aexp_sound; reflexivity). 
  replace (aeval st a0) with (aeval st a0') by (subst a0'; rewrite <- optimize_0plus_aexp_sound; reflexivity).
  reflexivity.

  unfold bequiv in *. simpl. intros. rewrite <- IHb. 
  reflexivity. 

  unfold bequiv in *. intros. simpl. rewrite <- IHb1; rewrite <- IHb2. reflexivity.     



Qed.

