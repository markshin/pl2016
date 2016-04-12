Require Import P09.



Check ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.

