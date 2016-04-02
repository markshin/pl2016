Require Export D.



(** **** Problem #4 : 2 stars (beq_natlist) *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. 

    You can use [beq_nat] from Basics.v
*)

Check beq_nat.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, h::t => false
  | h::t, nil => false
  | h1::t1, h2::t2 => match beq_nat h1 h2 with
                        | true => beq_natlist t1 t2
                        | false => false
  end
  end.

Example test_beq_natlist1 :   beq_natlist nil nil = true.
Proof. reflexivity. Qed.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

(** Hint: You may need to first prove a lemma about reflexivity of beq_nat. *)
Theorem beq_natlist_refl : forall l:natlist,
  beq_natlist l l = true.
Proof.
  intros.
  induction l.
  simpl. reflexivity.
  induction n.
  simpl.
  rewrite -> IHl.
  reflexivity.
  rewrite <- IHn. simpl. reflexivity.
Qed.
  
(** [] *)

