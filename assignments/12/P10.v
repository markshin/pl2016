Require Export P09.



(** Write a type inference function [tyeq: tm -> option ty].
**)
Print tm. 
Print ty.


Fixpoint tyinfer (t: tm) : option ty :=
    match t with
    | ttrue => Some TBool
    | tfalse => Some TBool
    | tif t1 t2 t3 => match (tyinfer t1) with 
                | Some TBool => match (tyinfer t2) with
                                | Some TBool => match (tyinfer t3) with
                                    |Some TBool => Some TBool
                                    |Some TNat => None
                                    | None => None
                                    end
                                | Some TNat => match (tyinfer t3) with
                                    |Some TBool => None
                                    | Some TNat => Some TNat
                                    | None => None
                                    end
                                | None => None
                                end
                | Some TNat => None
                | None => None
                end
    | tzero => Some TNat
    | tsucc t => match (tyinfer t) with
                | Some TBool => None
                | Some TNat => Some TNat
                | None => None
                end
    | tpred t => match (tyinfer t) with
                | Some TBool => None
                | Some TNat => Some TNat
                | None => None
                end
    | tiszero t => match (tyinfer t) with
                | Some TBool => None
                | Some TNat => Some TBool
                | None => None
                end
    
    end.



Example tyinfer_ex1:
  tyinfer
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
  = Some TBool.
Proof. reflexivity. Qed.

Example tyinfer_ex2:
  tyinfer
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
  = None.
Proof. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tyinfer_correct1: forall t T
    (TYCHK: tyinfer t = Some T),
  |- t \in T.
Proof.
  exact GIVEUP. 



Qed.

Theorem tyinfer_correct2: forall t T
    (HASTY: |- t \in T),
  tyinfer t = Some T.
Proof.
  intros.
  generalize dependent T.
  induction t; intros.
  - inversion T; inversion HASTY. auto. auto. 
  - inversion T; inversion HASTY. auto. auto.
  - inversion T; inversion HASTY; subst. apply IHt1 in H2.
    apply IHt2 in H4. apply IHt3 in H5. simpl.  rewrite H2. rewrite H4.
    rewrite H5. auto.  eauto.  destruct T.  reflexivity. reflexivity.
    apply IHt1 in H2. apply IHt2 in H4. apply IHt3 in H5.
    simpl. rewrite H2. rewrite H4. rewrite H5. destruct T. 
    reflexivity. reflexivity.
  - inversion T; inversion HASTY. auto. auto. 
  - inversion T; inversion HASTY. apply IHt in H0. simpl. 
    rewrite H0. reflexivity.
    apply IHt in H0. simpl. rewrite H0. reflexivity.
  -  inversion T; inversion HASTY. apply IHt in H0. simpl. 
    rewrite H0. reflexivity.
    apply IHt in H0. simpl. rewrite H0. reflexivity.
  -  inversion T; inversion HASTY. apply IHt in H0. simpl. 
    rewrite H0. reflexivity.
    apply IHt in H0. simpl. rewrite H0. reflexivity.  



Qed.

