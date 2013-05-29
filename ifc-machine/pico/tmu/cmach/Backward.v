Require Import List.

Require Import Utils.
Require Import Concrete.
Require Import ConcreteMachineSmallStep.
Require TINI.

Set Implicit Arguments.

Section Backward.

Let ctrace := list (option CEvent).
Let exec := TINI.exec cstep.

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

Lemma kernel_run_until_user_r : forall s s',
                                  kernel_run_until_user s s' ->
                                  priv s' = false.
Proof.
  intros. induction H; auto.
Qed.

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

Let cons_event e t : ctrace :=
  match e with
    | Some _ => e :: t
    | None => t
  end.

Inductive cexec : CS -> ctrace -> CS -> Prop :=
| ce_refl : forall s, cexec s nil s
| ce_kernel_end : forall s s', kernel_run s s' -> cexec s nil s'
| ce_kernel_user : forall s s' t s'',
                     kernel_run_until_user s s' ->
                     cexec s' t s'' ->
                     cexec s t s''
| ce_user_step : forall s e s' t s'',
                   priv s = false ->
                   cstep s e s' ->
                   cexec s' t s'' ->
                   cexec s (cons_event e t) s''.
Hint Constructors cexec.

Lemma cexec_step : forall s e s' t s''
                          (Hstep : cstep s e s')
                          (Hexec : cexec s' t s''),
                          cexec s (cons_event e t) s''.
Proof.
  (* Automation disaster.... :( *)
  intros.
  inv Hexec; simpl;
  destruct (priv s) eqn:Hs; eauto.

  - destruct (priv s'') eqn:Hs'; eauto;

    (* congruence is not working here... *)
    inversion Hstep; subst; simpl in *;
    repeat match goal with
             | H : false = true |- _ =>
               inversion H
             | H : true = false |- _ =>
               inversion H
             | H : ?x = ?x |- _ => clear H
           end; eauto.

    eapply ce_kernel_user; eauto; solve [eauto].

  - generalize (kernel_run_l H). intros H'.

    inversion Hstep; subst; simpl in *;
    repeat match goal with
             | H : false = true |- _ =>
               inversion H
             | H : true = false |- _ =>
               inversion H
             | H : ?x = ?x |- _ => clear H
           end; eauto.

  - generalize (kernel_run_until_user_l H). intros H'.

    inversion Hstep; subst; simpl in *;
    repeat match goal with
             | H : false = true |- _ =>
               inversion H
             | H : true = false |- _ =>
               inversion H
             | H : ?x = ?x |- _ => clear H
           end; eauto.

  - inversion Hstep; subst; simpl in *;
    repeat match goal with
             | H : false = true |- _ =>
               inversion H
             | H : true = false |- _ =>
               inversion H
             | H : ?x = ?x |- _ => clear H
           end; eauto.

    subst.
    eapply ce_kernel_user; eauto.
    eapply kruu_end; eauto.
    eauto.

    eauto.
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

End Backward.
