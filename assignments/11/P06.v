Require Export P05.



Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2. 
  generalize dependent y2. 
  
  
  induction P11; intros.
  inversion P21; subst; try reflexivity. 
  exfalso. apply P12. exists y. assumption.


    apply IHP11; try assumption. 
    inversion P21; subst. 
    exfalso. apply P22. exists y. assumption.
  
    assert (k := step_deterministic_alt x y0 y).
    assert (y0 = y). apply k. assumption. assumption. 
    subst. assumption.  
    
(* We recommend using this initial setup as-is! *)
Qed.

