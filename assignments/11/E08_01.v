Require Import P08.


Check eval__multistep : forall t n,
  t || n -> t ==>* C n.

