Require Import P10.


Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.

