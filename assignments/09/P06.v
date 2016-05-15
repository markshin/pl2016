Require Export P05.



Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  unfold ctrans_sound.
  unfold constfold_0plus.
  intros.
  remember (fold_constants_com c) as c'.
  apply trans_cequiv with c'. rewrite Heqc'. apply fold_constants_com_sound.
  apply optimize_0plus_com_sound. 
Qed.

