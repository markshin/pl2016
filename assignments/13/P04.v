Require Export P03.



Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  exact GIVEUP.
Qed.

