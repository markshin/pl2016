Require Import P02.


Check typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.

