Require Import P11.



Check pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).

