Require Export D.



(** 1 star (double_even)  *)
Theorem double_even : forall n,
  ev (double n).
Proof.
  exact GIVEUP.
Qed.

(** 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  exact GIVEUP.
Qed.

(** 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  exact GIVEUP.
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

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  exact GIVEUP.
Qed.

