Require Export D.



(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)

Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : bevalR (BTrue) true
| E_Bfalse : bevalR (BFalse) false
| E_BEq : forall (a1 a2 : aexp) (n1 n2 : nat), aevalR a1 n1 -> aevalR a2 n2 -> bevalR (BEq a1 a2) (beq_nat n1 n2)
| E_BLe : forall (a1 a2 : aexp) (n1 n2 : nat), aevalR a1 n1 -> aevalR a2 n2 -> bevalR (BLe a1 a2) (ble_nat n1 n2)
| E_BNot: forall (b1 : bexp) (b : bool), bevalR b1 b -> bevalR (BNot b1) (negb b)
| E_BAnd: forall (b1 b2 : bexp) (bo1 bo2 : bool), bevalR b1 bo1 -> bevalR b2 bo2 -> bevalR (BAnd b1 b2) (andb bo1 bo2)
.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  Proof.
  split.
  intros.
  induction H; simpl in * ; try (apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0) ; subst; reflexivity.

  generalize dependent bv.
  induction b; intros; simpl in *; subst; constructor; try(rewrite aeval_iff_aevalR); try (apply IHb); try (apply IHb1); try (apply IHb2); reflexivity.
Qed.

