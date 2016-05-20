Require Import P05.


Check progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

