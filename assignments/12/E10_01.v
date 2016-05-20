Require Import P10.



Check (conj tyinfer_ex1 tyinfer_ex2 :
  (tyinfer
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
  = Some TBool)
  /\
  (tyinfer
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
  = None)).

Check tyinfer_correct1: forall t T
    (TYCHK: tyinfer t = Some T),
  |- t \in T.

Check tyinfer_correct2: forall t T
    (HASTY: |- t \in T),
  tyinfer t = Some T.
