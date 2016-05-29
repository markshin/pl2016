Require Export P14.



(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  induction b; eauto; right.
remember (aexp_strong_progress st a) as Ha1.
remember (aexp_strong_progress st a0) as Ha2.
destruct Ha1 as [[? ?] | [? ?]]; destruct Ha2 as [[? ?] | [? ?]]; subst; eauto.

remember (aexp_strong_progress st a) as Ha1.         remember (aexp_strong_progress st a0) as Ha2.             destruct Ha1 as [[? ?] | [? ?]]; destruct Ha2 as [[? ?] | [? ?]]; subst; eauto.

destruct IHb as [[? | ?] | [? ?]]; subst; eauto. 

destruct IHb1 as [[? | ?] | [? ?]]; 
destruct IHb2 as [[? | ?] | [? ?]]; subst; eauto.

Qed.



