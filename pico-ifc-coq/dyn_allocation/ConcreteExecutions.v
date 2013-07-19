Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Instr Memory.
Require Import Concrete.
Require Import ConcreteMachine.
Require Import Determinism.
Require TINI.
Open Scope Z_scope.

Set Implicit Arguments.

Section CExec.
(* These are general definitions for the code generation *)
(* Could be put in CodeSpec.v *)

Notation block := (block privilege).
Variable cblock : block.

Inductive runsUntilUser : CS -> CS -> Prop :=
| ruu_end : forall s s',
              priv s = true ->
              priv s' = false ->
              cstep cblock s None s' ->
              runsUntilUser s s'
| ruu_step : forall s s' s'',
               priv s = true ->
               cstep cblock s None s' ->
               runsUntilUser s' s'' ->
               runsUntilUser s s''.
Hint Constructors runsUntilUser.

Lemma runsUntilUser_l : forall s s',
                                  runsUntilUser s s' ->
                                  priv s = true.
Proof.
  intros. inv H; trivial.
Qed.
Hint Resolve runsUntilUser_l.

Lemma runsUntilUser_r : forall s s',
                                  runsUntilUser s s' ->
                                  priv s' = false.
Proof.
  intros. induction H; auto.
Qed.

Lemma runsUntilUser_star :
  forall cs cs',
    runsUntilUser cs cs' ->
    star (cstep cblock) cs nil cs'.
Proof. induction 1; eauto. Qed.
Hint Resolve runsUntilUser_star.

Lemma runsUntilUser_determ :
  forall s1 s21 s22
         (RUN1 : runsUntilUser s1 s21)
         (RUN2 : runsUntilUser s1 s22),
    s21 = s22.
Proof.
  intros.
  induction RUN1; inv RUN2;
  try match goal with
        | [ H1 : cstep _ ?s _ _,
            H2 : cstep _ ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_determ H1 H2);
          intros [? ?]; subst
      end; eauto;
  try match goal with
        | [ H : runsUntilUser _ _ |- _ ] =>
          generalize (runsUntilUser_l H);
          intros
      end;
  congruence.
Qed.

Inductive runsToEnd : CS -> CS -> Prop :=
| rte_refl : forall s, priv s = true -> runsToEnd s s
| rte_step : forall s s' s'',
               priv s = true ->
               cstep cblock s None s' -> (* slippery to put None, but justified *)
               runsToEnd s' s'' ->
               runsToEnd s s''.
Hint Constructors runsToEnd.

Lemma runsToEnd_l : forall s s',
                       runsToEnd s s' ->
                       priv s = true.
Proof.
  intros. inv H; trivial.
Qed.

Lemma runsToEnd_r : forall s s',
                       runsToEnd s s' ->
                       priv s' = true.
Proof.
  intros. induction H; auto.
Qed.

Lemma runsToEnd_star :
  forall cs cs',
    runsToEnd cs cs' ->
    star (cstep cblock) cs nil cs'.
Proof. induction 1; eauto. Qed.
Hint Resolve runsToEnd_star.

Lemma runsToEnd_trans : forall cs1 cs2 cs3,
                           runsToEnd cs1 cs2 ->
                           runsToEnd cs2 cs3 ->
                           runsToEnd cs1 cs3.
Proof. induction 1; eauto. Qed.
Hint Resolve runsToEnd_trans.

Lemma runsUntilUser_trans : forall s1 s2 s3,
                                      runsToEnd s1 s2 ->
                                      runsUntilUser s2 s3 ->
                                      runsUntilUser s1 s3.
Proof. induction 1; eauto. Qed.

Inductive runsToEscape : CS -> CS -> Prop :=
| rte_success: (* executing until a return to user mode, all state in priv mode *)
    forall cs cs',
    forall (STAR: runsUntilUser cs cs' ),
      runsToEscape cs cs'
| rte_fail : (* executing the tmu until it fails at a neg. pc in priv mode, all in priv mode *)
    forall cs cs',
    forall (STAR: runsToEnd cs cs')
           (FAIL: fst (pc cs') < 0),
      runsToEscape cs cs'.

Lemma runsToEscape_plus: forall s1 s2,
 runsToEscape s1 s2 ->
 s1 <> s2 ->
 plus (cstep cblock) s1 nil s2.
Proof.
  induction 1 ; intros; eauto.
Qed.

Lemma runsToEscape_star: forall s1 s2,
 runsToEscape s1 s2 ->
 star (cstep cblock) s1 nil s2.
Proof.
  inversion 1; eauto.
Qed.


End CExec.

Hint Constructors runsUntilUser runsToEnd.
Hint Resolve runsUntilUser_l runsUntilUser_r.
