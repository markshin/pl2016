Require Export D.



(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
    match e with
    | ANum n => [SPush n]
    | AId i => [SLoad i]
    | APlus a b => (s_compile a) ++ (s_compile b) ++ [SPlus]
    | AMinus a b => (s_compile a) ++ (s_compile b) ++ [SMinus]
    | AMult a b => (s_compile a) ++ (s_compile b) ++ [SMult]
    end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *) 
Inductive step : state -> list nat -> sinstr -> list nat -> Prop :=
| step0 : forall st s n, step st s (SPush n) (n::s)
| step1 : forall st s i, step st s (SLoad i) (st i::s)
| step2 : forall st s a b, step st (a::b::s) SPlus (b+a::s)
| step3 : forall st s a b, step st (a::b::s) SMinus (b-a::s)
| step4 : forall st s a b, step st (a::b::s) SMult (b*a::s).

Inductive steps : state -> list nat -> list sinstr -> list nat -> Prop :=
| steps0 : forall st s, steps st s [] s
| steps1 : forall st s1 s2 s3 instr instrs,
    step st s1 instr s2 -> steps st s2 instrs s3 ->
    steps st s1 (instr::instrs) s3.

Lemma steps_execute : forall s st stk1 stk2,
    steps st stk1 s stk2 -> s_execute st stk1 s = stk2.
Proof.
  induction 1. reflexivity. 
  inversion H; subst; simpl; auto.
Qed.

Lemma steps_app : forall i1 i2 st s0 s1 s2,
    steps st s0 i1 s1 ->
    steps st s1 i2 s2 ->
    steps st s0 (i1 ++ i2) s2.
Proof.
  induction i1; simpl; intros.
  inversion H; subst; auto.
  inversion H; subst; auto.
  inversion H5; subst; econstructor; try constructor; eapply IHi1; eassumption.
Qed.

Lemma s_compile_steps : forall st e init,
    steps st init (s_compile e) ( aeval st e :: init ).
Proof.
  induction e; simpl; intros; repeat econstructor;
  repeat (eapply steps_app; try apply IHe1; try apply IHe2); repeat econstructor.
Qed.
  
Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply steps_execute. apply s_compile_steps.
Qed.
   
