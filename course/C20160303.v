(*
Inductive nat : Type :=
| O : nat
| S : nat -> nat
.
*)

Check (S(S(S O))).

Check (nat -> nat : Type).

Check (S).

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S m => S(S(double m))
  end.

Check double.

Eval compute in (double (S(O))).

Print plus.

Print Nat.add.

Eval compute in ((plus 3) 5).

Check plus.

Inductive even : nat -> Type :=
| EO : even 0
| ESS {n: nat} : even n -> even (S(S n))
.
Hint Constructors even.

Check (@ESS).

Check (ESS EO).

Check (plus : nat -> nat -> nat).

Check (
forall n : nat, even (S (S n)) -> even n : Type
).

Fixpoint proof_even_minus_two n (p: even (S(S n))) : even n :=
  match p with
  | @ESS n p' => p'
  end.

Eval compute in 
(proof_even_minus_two 2 (ESS (ESS EO))).

Fixpoint proof_even_ss n : 
  forall m, even (n+m) -> even (S n + S m) :=
  match n return forall m, even (n+m) -> even (S n + S m) with
  | 0 => fun m p => ESS p
  | 1 => fun m p => ESS p
  | S (S n') => fun m p => ESS (proof_even_ss n' m (proof_even_minus_two _ p))
  end.

Fixpoint proof_even (n: nat) : even (n+n) :=
  match n return even (n+n) with
  | 0 => EO
  | S n' => proof_even_ss n' n' (proof_even n')
  end.

Eval compute in proof_even 3.

Check proof_even.

Eval compute in proof_even 7.

Theorem proof_even': forall n : nat, even (n+n).
Proof.
  induction n.
  - simpl. auto.
  - simpl. rewrite <- plus_n_Sm. auto.
Defined.

Print proof_even'.

Require Import Omega.

Fixpoint sum (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => sum m + n
  end.

Eval compute in (sum 6).

Definition sum_eqn: 
  forall n : nat, 2 * sum n = n * (n + 1).
Proof.
  induction n.
  - auto.
  - simpl.
    rewrite (mult_plus_distr_l n 1).
    rewrite <- IHn. 
    omega.
Qed.

Print sum_eqn.

Check (0: nat).

Lemma foo: forall n,
  (n+n)*2 = 4*n.
Proof.
intros.
omega.
Qed.

