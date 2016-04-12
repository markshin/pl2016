Require Import P11.



Check pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.

