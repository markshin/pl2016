Require Import Arith NPeano.

(** Important: 
    - You are NOT allowed to use the [admit] tactic
      because [admit] simply admits any goal 
      regardless of whether it is provable or not.

      But, you can leave [admit] for problems that you cannot prove.
      Then you will get zero points for those problems.

    - You are NOT allowed to use the following tactics.

      [tauto], [intuition], [firstorder], [omega].

    - Here is the list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [apply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [auto]
      [repeat]
      [try]
      [;]
**)

Definition admit {T: Type} : T.  Admitted.

(**
  Definition of [list] 
 **)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments app {X} l1 l2.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Check (3 :: ([0; 1] ++ [])).

(**
  You may want to use the following lemmas.
 **)

Check mult_comm.
Check mult_1_r.
Check mult_assoc.
Check plus_comm.
Check plus_0_r.
Check plus_assoc.
Check plus_minus.
Check mult_plus_distr_l.
Check mult_plus_distr_r.
Check mult_minus_distr_l.
Check mult_minus_distr_r.

Check le_not_lt.
Check lt_le_trans.
Check lt_irrefl.

(*=========== 3141592 ===========*)

(** Easy:
    Prove the following theorem.
 **)

Lemma forall_not_ex_not: forall (X: Type) (P: X -> Prop)
    (ALL: forall x, P x),
  ~ exists x, ~ P x.
Proof.
  intros.
  unfold not.
  intros. 
  destruct H. 
  apply H.
  apply ALL.
Qed.

(*=========== 3141592 ===========*)

(** Easy:
    Define a function [square_sum] satisfying:

      square_sum n = 1^2 + 2^2 + ... +n^2

 **)

Fixpoint square_sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S n => (S n * S n) + square_sum n
  end.

Example square_sum_example1: square_sum 5 = 55.
Proof. reflexivity. Qed.

Example square_sum_example2: square_sum 10 = 385.
Proof. reflexivity.  Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Define a function [fibonacci] satisfying:

      fibonacci 0 = 0
      fibonacci 1 = 1
      fibonacci (n+2) = fibonacci (n+1) + fibonacci n

 **)

Fixpoint fibonacci (n: nat) : nat :=
  match n with
  | 0 => 0
  | S 0 => 1
  | S n' => fibonacci (n') + fibonacci (n'-1)
  end.

Example fibonacci_example1: fibonacci 5 = 5.
Proof. reflexivity. Qed.

Example fibonacci_example2: fibonacci 10 = 55.
Proof. reflexivity. Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Fixpoint odd_sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => 1 + 2*m + odd_sum m
  end.

Theorem odd_sum__square: forall n,
  odd_sum n = n * n.
Proof.
  intros.
  induction n. 
  simpl. reflexivity.
  simpl. rewrite -> IHn. 
    apply f_equal. rewrite -> plus_comm with (n := n) (m := n +0 ).
    rewrite -> plus_0_r.
     rewrite <- mult_n_Sm.
    rewrite -> plus_assoc.
    rewrite -> plus_comm with (n := n) (m := n *n). rewrite -> plus_comm with (n := n + n) (m := n* n).
    rewrite -> plus_assoc.
    reflexivity.
Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Lemma app_tail_cancel: forall X (l1 l2: list X) a
    (EQ: l1 ++ [a] = l2 ++ [a]),
  l1 = l2.
Proof.
    intros.
   generalize dependent l2.
   induction l1.
   destruct l2.
   intros. reflexivity.
   intros. inversion EQ. destruct l2.
   inversion H1. inversion H1.
   destruct l2.
   intros. inversion EQ. destruct l1. inversion H1.
   inversion H1.
   intros.
   inversion EQ.
   apply IHl1 in H1. rewrite  H1.
    reflexivity.
Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Lemma odd_or_even: forall n,
  exists k, n = 2*k \/ n = 1 + 2*k.
Proof.
  intros.
  induction n. 
  exists 0. 
  left. reflexivity.
  destruct IHn.
  inversion H.
  exists x.
  right. rewrite <- H0. simpl. reflexivity.
  exists (1+x).
  left.
  rewrite -> H0.
  simpl. rewrite plus_n_Sm. reflexivity. 
Qed.

(*=========== 3141592 ===========*)

(** Hard:
    Prove the following theorem.
 **)

Lemma two_three_rel_prime: forall n m
    (EQ: 2 * n = 3 * m),
  exists k, m = 2 * k.
Proof.
  intros.

  generalize dependent m.
  induction n.
  intros.
  destruct m. 
  exists 0. reflexivity.
  simpl in EQ. inversion EQ.
  intros.
  destruct m.
  simpl in EQ. inversion EQ.
  
simpl. 
  simpl in EQ.
admit.
Qed.

(*=========== 3141592 [30] ===========*)

(** Easy:
    Define a predicate [sorted_min: nat -> list nat -> Prop], where
    [sorted_min n l] holds iff the elements in the list [l] is greater
    than or equal to [n] and sorted in the increasing order.
 **)

Inductive sorted_min: nat -> list nat -> Prop :=
    | sort_0 : forall (n : nat), sorted_min n []
    | sort_2 : forall (n m : nat) (l : list nat), n <= m -> sorted_min n l -> sorted_min n (m :: l).


Example sorted_min_example1: sorted_min 0 [1; 3; 4; 4; 5].
Proof. admit. Qed.


Example sorted_min_example2: sorted_min 2 [2; 2; 3; 6].
Proof. (* FILL IN HERE *) admit. Qed.

Example sorted_min_non_example1: sorted_min 1 [0; 1] -> False.
Proof. (* FILL IN HERE *) admit. Qed.





(** Medium:
    Prove the following theorem. 
 **)

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Lemma sorted_not_in: forall n m l
    (SORTED: sorted_min m l)
    (LT: n < m),
  ~ appears_in n l.
Proof.
    unfold lt.
  intros.
  unfold not.
  intros.
  induction SORTED.
  inversion H.
  apply IHSORTED.
  apply LT.
  
  intros.
  inversion H. rewrite <- H1 in H.
  rewrite <- H1 in SORTED.
  apply IHl. apply SORTED.
Qed.









(** Hard:
    Prove the following theorem.
 **)

(* [beq_nat n m] returns [true]  if [n = m] holds; 
                 returns [false] otherwise. *)
Check beq_nat.
Check beq_nat_false.
Check beq_nat_true.
Check beq_nat_refl.

(* [ltb n m] returns [true]  if [n < m] holds; 
             returns [false] otherwise.
   Note that [ltb n m] is displayed as [n <? m]. *)
Check ltb.
Check ltb_lt.

Fixpoint appears_inb (n: nat) (l: list nat) : bool :=
  match l with
  | nil => false
  | m :: l' => 
    if ltb n m
    then false
    else (if beq_nat n m
          then true
          else appears_inb n l')
  end.

Theorem appears_inb_correct: forall n l
    (SORTED: sorted_min 0 l)
    (NOTAPPEAR: appears_inb n l = false),
  ~ appears_in n l.
Proof.
  (* FILL IN HERE *) admit.
Qed.

