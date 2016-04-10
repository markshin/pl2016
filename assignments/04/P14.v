Require Export D.
  
Theorem rev_snoc: forall (X: Type) (n : X) (l:list X), rev (snoc l n) = n :: (rev l).
Proof.
    intros.
    induction l as [ | n' l'].
    reflexivity.
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros.
  induction l as [ | n l'].
  simpl. reflexivity.
 simpl. rewrite -> rev_snoc.
 rewrite -> IHl'. reflexivity.
Qed.

(** **** Problem #13 : 3 stars (apply_exercise1)  *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     rev l = l'.
Proof.
  intros.
  induction l'.
  rewrite -> H.
  rewrite -> rev_involutive. reflexivity.
  rewrite -> H. rewrite -> rev_involutive. reflexivity.
Qed.

