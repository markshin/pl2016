Require Export D.



(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
Proof.
  apply E_Seq with (update empty_state X 0).
  apply E_Ass. reflexivity.
  apply E_Seq with (update (update empty_state X 0) Y 1).
  apply E_Ass. reflexivity. 
  apply E_Ass. reflexivity.
Qed.

