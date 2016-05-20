Require Import P02.


Check value_is_nf : forall t,
  value t -> step_normal_form t.

