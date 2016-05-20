Require Import P06.


Check preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

