Require Import P09.



Check ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).

