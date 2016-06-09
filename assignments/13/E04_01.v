Require Import P04.


Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').

