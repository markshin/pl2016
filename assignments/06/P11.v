Require Export D.



(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
    | pal_nil : pal []
    | pal_c1 : forall x, pal [x]
    | pal_cc : forall x l, pal l -> pal ( x :: l ++ [x]).


Example test_pal_1: pal [0; 1; 0].
Proof.
    assert (K : [0 ;1;0] = 0 :: ([1] ++ [0])).
    simpl. reflexivity.
    rewrite K.
    apply pal_cc. apply pal_c1.

Qed.

Lemma K : forall (X: Type) (l: list X) (x : X),
    snoc l x = l ++ [x].
Proof.
    intros.
    induction l.
    simpl. reflexivity.
    simpl. rewrite -> IHl.
    reflexivity.
Qed.

Lemma L : forall (X : Type) (l k p : list X),
    l ++ (k ++ p) = (l ++ k) ++ p.
Proof.
    intros.
    induction l.
    simpl. reflexivity.
    simpl. rewrite IHl.
    reflexivity.
Qed.

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros.
  induction l.
    simpl. apply pal_nil.
    simpl. 
    rewrite -> K.
    rewrite -> L.
    apply pal_cc.
    apply IHl.
Qed.

Lemma M : forall (X : Type) (l : list X) (x : X), rev(l ++ [x]) = x :: rev l.
Proof.
    intros.
    induction l. 
    simpl. reflexivity.
    simpl. rewrite -> IHl. rewrite -> K.
    rewrite -> K. simpl. reflexivity.
Qed.



Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros.
  induction H.
  simpl. reflexivity.
  simpl. reflexivity. 
    simpl. rewrite -> K. 
    rewrite -> M. rewrite <- IHpal.
    simpl. reflexivity. 
Qed.






