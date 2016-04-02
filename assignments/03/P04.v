Require Export D.


Lemma rev_snoc : forall (n : nat) (l : natlist), 
    rev (snoc l n)= n :: rev l.
Proof. 
    intros.
    induction l.
    simpl. reflexivity.
    simpl. rewrite -> IHl. 
    simpl. reflexivity.
Qed.


(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [ | n l'].
  simpl. reflexivity.
  simpl. 
  rewrite -> rev_snoc.  
  rewrite -> IHl'.
  reflexivity.
Qed.

