Require Export P05.



Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
  exact GIVEUP.
Qed.

