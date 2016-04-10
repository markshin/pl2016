Require Export D.



(** **** Problem #6 : 3 stars (map_rev) *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Lemma map_snoc : forall (X Y : Type) (f : X -> Y) (x : X) (l : list X),
    map f (snoc l x) = snoc (map f l) (f x).
Proof.
    intros.
    induction l.
    simpl. reflexivity.
    simpl. rewrite -> IHl.
    reflexivity.
Qed.


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  simpl. reflexivity.
  simpl. rewrite <- IHl.
  rewrite -> map_snoc.
  reflexivity.
Qed.

