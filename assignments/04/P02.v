Require Export D.



(** **** Problem #1 : 2 stars, optional (poly_exercises) *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Fill in the definitions
    and complete the proofs below. *)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
  | O => []
  | S n' => n :: repeat n n'
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  intros.
  induction l.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros.
  induction l1.
  simpl. reflexivity.
  simpl. rewrite IHl1.
  reflexivity.
Qed.

