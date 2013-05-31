Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import TMUInstr.
Require Import Concrete.
Require Import ConcreteMachineSmallStep.
Require TINI.
Open Scope Z_scope.

Set Implicit Arguments.

Section CExec.

(* congruence fails if these are let-bound *)
Local Notation ctrace := (list (option CEvent)).
Local Notation exec := (TINI.exec cstep).

Inductive kernel_run_until_user : CS -> CS -> Prop :=
| kruu_end : forall s s',
               priv s = true ->
               priv s' = false ->
               cstep s None s' ->
               kernel_run_until_user s s'
| kruu_step : forall s s' s'',
                priv s = true ->
                cstep s None s' ->
                kernel_run_until_user s' s'' ->
                kernel_run_until_user s s''.
Hint Constructors kernel_run_until_user.

Lemma kernel_run_until_user_l : forall s s',
                                  kernel_run_until_user s s' ->
                                  priv s = true.
Proof.
  intros. inv H; trivial.
Qed.
Hint Resolve kernel_run_until_user_l.

Lemma kernel_run_until_user_r : forall s s',
                                  kernel_run_until_user s s' ->
                                  priv s' = false.
Proof.
  intros. induction H; auto.
Qed.

Lemma kernel_run_until_user_star :
  forall cs cs',
    kernel_run_until_user cs cs' ->
    star cstep cs nil cs'.
Proof. induction 1; eauto. Qed.
Hint Resolve kernel_run_until_user_star.

Inductive kernel_run : CS -> CS -> Prop :=
| kr_refl : forall s, priv s = true -> kernel_run s s
| kr_step : forall s s' s'',
              priv s = true ->
              cstep s None s' ->
              kernel_run s' s'' ->
              kernel_run s s''.
Hint Constructors kernel_run.

Lemma kernel_run_l : forall s s',
                       kernel_run s s' ->
                       priv s = true.
Proof.
  intros. inv H; trivial.
Qed.

Lemma kernel_run_r : forall s s',
                       kernel_run s s' ->
                       priv s' = true.
Proof.
  intros. induction H; auto.
Qed.

Lemma kernel_run_star :
  forall cs cs',
    kernel_run cs cs' ->
    star cstep cs nil cs'.
Proof. induction 1; eauto. Qed.
Hint Resolve kernel_run_star.

Lemma kernel_run_trans : forall cs1 cs2 cs3,
                           kernel_run cs1 cs2 ->
                           kernel_run cs2 cs3 ->
                           kernel_run cs1 cs3.
Proof. induction 1; eauto. Qed.
Hint Resolve kernel_run_trans.

Lemma kernel_run_until_user_trans : forall s1 s2 s3,
                                      kernel_run s1 s2 ->
                                      kernel_run_until_user s2 s3 ->
                                      kernel_run_until_user s1 s3.
Proof. induction 1; eauto. Qed.

Inductive runsToEscape : CS -> CS -> Prop :=
| rte_success: (* executing until a return to user mode *)
    forall cs cs',
    forall (STAR: kernel_run_until_user cs cs' ),
      runsToEscape cs cs'
| rte_fail : (* executing the tmu until it fails at a neg. pc in priv mode *)
    forall cs cs',
    forall (STAR: kernel_run cs cs')
           (FAIL: fst (pc cs') < 0),
      runsToEscape cs cs'
| rte_upriv: (* in unpriv. mode, it already escaped *)
    forall cs,
    forall (UPRIV: priv cs = false),
      runsToEscape cs cs.

Lemma step_star_plus :
  forall (S E: Type)
         (Rstep: S -> option E -> S -> Prop) s1 t s2
         (STAR : star Rstep s1 t s2)
         (NEQ : s1 <> s2),
    plus Rstep s1 t s2.
Proof.
  intros. inv STAR. congruence.
  clear NEQ.
  gdep e. gdep s1.
  induction H0; subst; eauto.
Qed.
Hint Resolve step_star_plus.

Lemma runsToEscape_plus: forall s1 s2,
 runsToEscape s1 s2 ->
 s1 <> s2 ->
 plus cstep s1 nil s2.
Proof.
  induction 1 ; intros; eauto.
Qed.

Lemma runsToEscape_star: forall s1 s2,
 runsToEscape s1 s2 ->
 star cstep s1 nil s2.
Proof.
  inversion 1; eauto.
Qed.

Lemma star_trans: forall S E (Rstep: S -> option E -> S -> Prop) s0 t s1,
  star Rstep s0 t s1 ->
  forall t' s2,
  star Rstep s1 t' s2 ->
  star Rstep s0 (t++t') s2.
Proof.
  induction 1.
  - auto.
  - inversion 1.
    + rewrite app_nil_r.
      subst; econstructor; eauto.
    + subst; econstructor; eauto.
      rewrite op_cons_app; reflexivity.
Qed.

Let cons_event e t : ctrace :=
  match e with
    | Some _ => e :: t
    | None => t
  end.

Inductive exec_end : CS -> CS -> Prop :=
| ee_refl : forall s, exec_end s s
| ee_kernel_end : forall s s', kernel_run s s' -> exec_end s s'
| ee_final_fault : forall s s' s'',
                     priv s = false ->
                     cstep s None s' ->
                     kernel_run s' s'' ->
                     exec_end s s''.
Hint Constructors exec_end.

Inductive cexec : CS -> ctrace -> CS -> Prop :=
| ce_end : forall s s', exec_end s s' -> cexec s nil s'
| ce_kernel_begin : forall s s' t s'',
                      kernel_run_until_user s s' ->
                      cexec s' t s'' ->
                      cexec s t s''
| ce_user_hit : forall s e s' t s'',
                  priv s = false ->
                  cstep s e s' ->
                  priv s' = false ->
                  cexec s' t s'' ->
                  cexec s (cons_event e t) s''
| ce_user_miss : forall s s' s'' t s''',
                   priv s = false ->
                   cstep s None s' ->
                   kernel_run_until_user s' s'' ->
                   cexec s'' t s''' ->
                   cexec s t s'''.
Hint Constructors cexec.

Lemma priv_no_event_l : forall s e s'
                               (STEP : cstep s e s')
                               (PRIV : priv s = true),
                          e = None.
Proof.
  intros.
  inv STEP; simpl in *; try congruence; auto.
Qed.

Lemma priv_no_event_r : forall s e s'
                               (STEP : cstep s e s')
                               (PRIV : priv s' = true),
                          e = None.
Proof.
  intros.
  inv STEP; simpl in *; try congruence; auto.
Qed.

Lemma exec_end_step : forall s e s' s''
                             (STEP : cstep s e s')
                             (EXEC : exec_end s' s''),
                        cexec s (cons_event e nil) s''.
Proof.
  intros.
  destruct (priv s) eqn:PRIV;
  [exploit priv_no_event_l; eauto; intros ?; subst|];
  (destruct (priv s') eqn:PRIV';
  [exploit priv_no_event_r; eauto; intros ?; subst|]);
  inv EXEC; eauto.
Qed.
Hint Resolve exec_end_step.

Lemma cexec_step : forall s e s' t s''
                          (Hstep : cstep s e s')
                          (Hexec : cexec s' t s''),
                          cexec s (cons_event e t) s''.
Proof.
  intros.
  inv Hexec; simpl; eauto;
  (destruct (priv s) eqn:PRIV;
   [assert (e = None) by (eapply priv_no_event_l; eauto); subst|]);
  eauto.
  - exploit priv_no_event_r; eauto.
    intros ?. subst.
    eauto.
  - subst. simpl.
    eapply ce_kernel_begin; eauto.
Qed.

Let remove_silent (ct : ctrace) :=
  filter (fun e => match e with Some _ => true | _ => false end) ct.

Lemma cons_event_remove_silent :
  forall e t,
    remove_silent (e :: t) = cons_event e (remove_silent t).
Proof.
  intros [e|] t; reflexivity.
Qed.

Lemma exec_cexec : forall s t s',
                     exec s t s' ->
                     cexec s (remove_silent t) s'.
Proof.
  intros s t s' Hexec.
  induction Hexec; eauto.
  rewrite cons_event_remove_silent.
  eapply cexec_step; eauto.
Qed.

End CExec.
