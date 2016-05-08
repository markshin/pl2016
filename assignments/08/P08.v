Require Export D.



(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
    intros. split; intros.
  inversion H; subst.
  apply E_IfFalse. simpl. rewrite H5. reflexivity. apply H6.
  apply E_IfTrue. simpl. rewrite H5. reflexivity. apply H6.
  inversion H; subst.
  apply E_IfFalse. simpl in H5. SearchAbout negb. apply negb_true_iff in H5.
  apply H5. apply H6.
  apply E_IfTrue. simpl in H5. apply negb_false_iff in H5. apply H5.
apply H6. 
Qed.

