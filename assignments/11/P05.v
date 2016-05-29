Require Export P04.



(** **** Exercise: 2 stars (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.

  eapply multi_step. apply ST_Plus2. apply v_const. apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst. 
  eapply multi_step. apply ST_Plus2. apply v_const. 
   apply ST_PlusConstConst. 
   apply multi_refl.
    
    Qed.

