Require Export P02.



(** **** Exercise: 4 stars (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

Theorem hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.
Proof.
 unfold hoare_triple. 
 unfold not. 
 exists (APlus (AId X) (ANum 1)).
 intros.

assert ( H1 := H empty_state (update empty_state X 1)).
assert (( X ::= APlus (AId X) (ANum 1)) / empty_state || update empty_state X 1).
constructor. simpl. reflexivity.
apply H1 in H0. simpl in H0. unfold update in H0. simpl in H0. inversion H0. auto.      
Qed.

