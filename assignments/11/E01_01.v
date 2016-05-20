Require Import P01.


Check test_step_2 : 
      P 
        (C 0)
        (P 
          (C 2) 
          (P (C 0) (C 3)))
      ==>
      P 
        (C 0)
        (P 
          (C 2) 
          (C (0 + 3))).

