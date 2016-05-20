Require Import P04.


Check succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.  

