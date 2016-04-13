Require Import P02.



Check nil_app : forall X:Type, forall l:list X,
  app [] l = l.

