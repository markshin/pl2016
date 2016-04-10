Require Export D.



(** **** Problem #20 : 3 stars (gen_dep_practice)  *)
(** Prove this by induction on [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros.
  generalize dependent n.
  induction l.
  simpl. reflexivity.
  destruct n. intros. inversion H.
  intros. apply IHl. simpl. inversion H.
  reflexivity.
Qed.

