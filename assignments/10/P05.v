Require Export P04.



(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.         
Check hoare_if. 
 remember (BLe (AId X) (AId Y)) as b.
    remember (fun st : state => st Y = st X + st Z) as R.
    remember (R [Z |-> AMinus (AId Y) (AId X)]) as Q1. 
   remember (R [Y |-> APlus (AId X) (AId Z)]) as Q2.
   eapply hoare_consequence_pre. 
    apply hoare_if; subst; apply hoare_asgn. 
unfold assert_implies, assn_sub, update. simpl. 
intros. 
split. intros. 
apply le_plus_minus. rewrite Heqb in H0. simpl in H0. 
apply ble_nat_true in H0. apply H0.
intros. reflexivity.  

Qed.

