Require Import P11.


Check evalF_eval : forall t n,
  evalF t = n <-> t || n.

