Require Export D.

Theorem plus_n_Sm : forall n m, S(n + m) = n + S m.
Proof.
    intros.
    induction n.
    simpl. reflexivity.
    simpl. rewrite -> IHn.
    reflexivity.
Qed.
(** **** Problem #18 : 3 stars (plus_n_n_injective)  *)
(** Practice using "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  { (* Hint: use the [destruct] and [inversion] tactics. *)
    simpl. destruct m.
    simpl. reflexivity.
    simpl. intros.
    inversion H.
  }
  { (* Hint: use the plus_n_Sm lemma *) 
    intros.
    destruct m.
    inversion H.
    rewrite <- plus_n_Sm in H. 
    rewrite <- plus_n_Sm in H.
    inversion H.
    apply IHn' in H1.
    rewrite -> H1.
    reflexivity.
  } 
Qed.

