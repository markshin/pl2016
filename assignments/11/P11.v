Require Export P10.



(** **** Exercise: 3 stars, optional (interp_tm)  *)
(** Remember that we also defined big-step evaluation of [tm]s as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.
 
    Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!  *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.

  split.
  generalize dependent n.  
  induction t.
  intros. simpl in *. rewrite H. constructor.
  intros. simpl in *. rewrite <- H.  constructor.
  apply IHt1. reflexivity.
  apply IHt2. reflexivity.
  intros.
  induction H. simpl. reflexivity.
  simpl. subst. reflexivity. 
    
    
    Qed.

