Require Export P02.



Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.

  unfold atrans_sound.
  induction a. simpl. apply refl_aequiv.
  simpl. apply refl_aequiv.
  {
  unfold aequiv in IHa1. unfold aequiv in IHa2.
  destruct a1; destruct a2; try (destruct n); try (destruct n0); unfold aequiv; intros; 
  assert (H1 := IHa1 st); assert(H2 := IHa2 st); simpl in *; try (rewrite H1); try (rewrite H2); try reflexivity; omega. }

  unfold aequiv in IHa1. unfold aequiv in IHa2.
  destruct a1; destruct a2; try (destruct n); try (destruct n0); unfold aequiv; intros; 
  assert (H1 := IHa1 st); assert(H2 := IHa2 st); simpl in *; try (rewrite H1); try (rewrite H2); try reflexivity; omega.

  
  unfold aequiv in IHa1. unfold aequiv in IHa2.
  destruct a1; destruct a2; try (destruct n); try (destruct n0); unfold aequiv; intros; 
  assert (H1 := IHa1 st); assert(H2 := IHa2 st); simpl in *; try (rewrite H1); try (rewrite H2); try reflexivity; omega.


Qed.

