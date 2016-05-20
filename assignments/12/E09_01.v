Require Import P09.


Check subject_expansion_false: 
  exists t t' T,
    t ==> t' /\
    |- t' \in T /\
    ~ |- t \in T.

