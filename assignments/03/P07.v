Require Export D.

Theorem snoc_append : forall (l:natlist) (n:nat),
    snoc l n = l ++ [n].
Proof.
    intros.
    induction l.
    simpl. reflexivity.
    simpl. rewrite -> IHl.
    reflexivity.
Qed.

Theorem app_nil_end : forall (l : natlist), 
    l ++ [] = l.
Proof.
    intros.
    induction l.
    reflexivity.
    simpl. rewrite -> IHl.
    reflexivity.
Qed. 

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros.
  induction l1.
  simpl. rewrite -> app_nil_end.
  reflexivity.
  simpl. rewrite -> IHl1.
  rewrite -> snoc_append.
  rewrite -> snoc_append.
  rewrite -> app_assoc.
  reflexivity.
Qed.

