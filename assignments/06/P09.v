Require Export D.



(** 1 star (double_even)  *)
Theorem double_even : forall n,
  ev (double n).
Proof.
 intros.
 induction n.
 simpl. apply ev_0.
 simpl. apply ev_SS. apply IHn. 
Qed.

(** 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros.
  induction H.
  simpl. apply H0.
  simpl. apply ev_SS.
  apply IHev.
Qed.

(** 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros.
  induction H0. simpl in H. apply H.
  simpl in H. inversion H. apply IHev. apply pf_evn.
Qed.

(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)

Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n +p).
Proof.
    intros.
    induction n. 
    simpl. reflexivity.
    simpl. rewrite <- plus_n_Sm. 
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  apply ev_sum with ( n:= n+m) (m := n+ p) in H.
  rewrite plus_swap in H.
  rewrite <- plus_assoc in H.
  rewrite -> plus_assoc with n n (m + p) in H.
  apply ev_ev__ev with (n := n+ n) (m := m+ p) in H.
  apply H.
  rewrite <- double_plus.
  apply double_even. apply H0.
Qed.








