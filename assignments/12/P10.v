Require Export P09.



(** Write a type inference function [tyeq: tm -> option ty].
**)

Fixpoint tyinfer (t: tm) : option ty :=
  GIVEUP.

Example tyinfer_ex1:
  tyinfer
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
  = Some TBool.
Proof. exact GIVEUP. Qed.

Example tyinfer_ex2:
  tyinfer
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
  = None.
Proof. exact GIVEUP. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tyinfer_correct1: forall t T
    (TYCHK: tyinfer t = Some T),
  |- t \in T.
Proof.
  exact GIVEUP.
Qed.

Theorem tyinfer_correct2: forall t T
    (HASTY: |- t \in T),
  tyinfer t = Some T.
Proof.
  exact GIVEUP.
Qed.

