Require Export D.


Theorem plus_0_r : forall n : nat,
    n + 0 = n.
Proof.
    intros.
    induction n as [ | n'].
    reflexivity.
    simpl. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
    intros.
    induction n as [ | n'].
    reflexivity.
    simpl. rewrite -> IHn'.
    reflexivity.
Qed.
(** **** Problem : 3 stars (mult_comm) *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n as [ | n']; induction m as [ | m'].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite plus_0_r. rewrite plus_0_r.
  reflexivity.
  simpl. rewrite -> IHn'. simpl. rewrite -> plus_assoc.
  reflexivity.
Qed.


Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
    intros.
    induction n as [ | n'].
simpl. reflexivity.
simpl. rewrite -> IHn'.
rewrite mult_plus_distr_r.
reflexivity.
Qed.

