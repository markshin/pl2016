Require Import P06.


Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

