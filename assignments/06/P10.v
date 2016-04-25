Require Export D.



(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  intros.
  induction n.
  split.
  intros. simpl. apply ev_0. 
  intros. apply ev_0.
  split. simpl.  apply IHn.

    intros. induction n. inversion H.
    simpl in IHn. induction IHn. apply ev_SS in H0. apply H0. inversion H. unfold even. apply H3. 
    
Qed.

Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
  intros.
  induction n.
  apply ev_0.
  apply even__ev_strong. 
  apply H.
Qed.

