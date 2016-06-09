Require Export P04.



(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Definition halve : tm :=
  GIVEUP.

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  (* unfold halve; eauto 10. *)
  exact GIVEUP.
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  exact GIVEUP.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  exact GIVEUP.
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
  exact GIVEUP.
Qed.

