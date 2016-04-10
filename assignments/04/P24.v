Require Export D.



(** **** Problem #23 : 2 stars (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intros. destruct b.
  destruct (f true) eqn:k. rewrite k. rewrite k. reflexivity.
  destruct (f false) eqn:l. rewrite k. reflexivity.
  rewrite l. reflexivity.
    destruct (f false) eqn:m. destruct (f true) eqn:n. rewrite n. reflexivity.
    rewrite m. reflexivity.
    rewrite m. rewrite m. reflexivity.

Qed.

