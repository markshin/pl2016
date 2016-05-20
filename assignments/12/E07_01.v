Require Import P07.


Check normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.

