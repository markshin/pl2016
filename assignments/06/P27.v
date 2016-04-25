Require Export D.



(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
    | all_nil : all P []
    | all_cons : forall x l, P x -> all P l -> all P ( x :: l) .  


(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Print forallb.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Example test_all_1: all (fun x => x = 1) [1; 1].
Proof. apply all_cons. reflexivity. apply all_cons. reflexivity. apply all_nil.  Qed.

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
  split.
  intros. 
    induction l. apply all_nil. apply all_cons.
    simpl in H. apply andb_true_elim1 in H. apply H.
    simpl in H. apply andb_true_elim2 in H. apply IHl in H.   apply H.
    intros.
    induction l. simpl.  reflexivity.
    simpl. inversion H. apply IHl in H3.
    rewrite -> H2. rewrite -> H3. reflexivity. 
Qed.

