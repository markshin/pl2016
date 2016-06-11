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
  tfix
  (tabs K (TArrow TNat TNat) 
    (tabs N TNat (tif0 (tvar N) (tnat 0)
                   (tif0 (tpred (tvar N)) (tnat 0)
                     (tsucc (tapp (tvar K) (tpred (tpred (tvar N))))))))).


Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
   unfold halve; eauto 10. 
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
   unfold halve; normalize. 
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
   unfold halve; normalize. 
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
 induction n.
- unfold halve. normalize.
- unfold halve in *. simpl. rewrite plus_comm. simpl.
    eapply multi_step. apply ST_AppFix. auto. auto. 
eapply multi_step. apply ST_App1. auto. simpl.
eapply multi_step. apply ST_AppAbs. auto. simpl. 
eapply multi_step. apply ST_If0Nonzero. 
eapply multi_step. apply ST_If01. apply ST_PredNat. simpl. 
eapply multi_step. apply ST_If0Nonzero. 
eapply multi_step. apply ST_Succ1. apply ST_App2. auto. apply ST_Pred. apply ST_PredNat. simpl.
    eapply multi_step. apply ST_Succ1. apply ST_App2. auto. apply ST_PredNat. simpl.


 assert ( K: forall t t', t ==>* t' -> tsucc t ==>* tsucc t').
    intros. induction H. constructor. 
eapply multi_step. apply ST_Succ1. apply H. 
assumption.     

 eapply multi_trans. apply K. 
apply IHn. eapply multi_step. apply ST_SuccNat. constructor.
Qed.

