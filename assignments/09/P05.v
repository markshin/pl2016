Require Export P04.



Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound.
  intros.
  induction c.
  simpl. apply refl_cequiv.

  simpl. apply CAss_congruence. apply optimize_0plus_aexp_sound.

  simpl. apply CSeq_congruence. assumption. assumption.   
  simpl. apply CIf_congruence. apply optimize_0plus_bexp_sound. assumption. assumption.

  simpl. apply CWhile_congruence. apply optimize_0plus_bexp_sound. assumption.


Qed.

