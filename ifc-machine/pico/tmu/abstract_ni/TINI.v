Require Import Relations.
Require Import List.

(**  Useful tactics **)
Ltac inv H := inversion H; clear H; subst.
Ltac gdep x := generalize dependent x.

Set Implicit Arguments.

Section Exec.

Variable state : Type.
Variable event : Type.
Variable step : state -> event -> state -> Prop.

Inductive exec : state -> list event -> state -> Prop :=
| e_refl : forall s, exec s nil s
| e_step : forall s e s' t s'',
             step s e s' ->
             exec s' t s'' ->
             exec s (e :: t) s''.

End Exec.

Class ObservableSemantics := {
  state : Type;
  event : Type;
  step : state -> event -> state -> Prop;

  observer : Type;

  e_equiv : observer -> relation event;
  e_low : observer -> event -> Prop;
  e_low_dec : forall o e, {e_low o e} + {~ e_low o e};
  e_equiv_low : forall o e1 e2, e_equiv o e1 e2 -> (e_low o e1 <-> e_low o e2);

  e_high_e_equiv : forall o e1 e2,
                     ~ e_low o e1 ->
                     ~ e_low o e2 ->
                     e_equiv o e1 e2
}.

Class UnwindingSemantics `{OS : ObservableSemantics} := {
  s_equiv : observer -> relation state;
  s_low : observer -> state -> Prop;
  s_low_dec : forall o s, {s_low o s} + {~ s_low o s};
  s_equiv_sym : forall o, symmetric _ (s_equiv o);
  s_equiv_low : forall o s1 s2, s_equiv o s1 s2 -> (s_low o s1 <-> s_low o s2);

  e_low_s_low : forall o s1 e s2,
                  step s1 e s2 ->
                  e_low o e ->
                  s_low o s1;

  (* Unwinding conditions *)

  equiv_trace_low: forall o s1 s2 e1 e2 s1' s2',
                     s_equiv o s1 s2 ->
                     s_low o s1 ->
                     step s1 e1 s1' ->
                     step s2 e2 s2' ->
                     e_equiv o e1 e2;

  lowstep : forall o t1 t2 s1 s1' s2 s2',
              s_equiv o s1 s2 ->
              s_low o s1 ->
              step s1 t1 s1' ->
              step s2 t2 s2' ->
              s_equiv o s1' s2';

  highstep : forall o s1 s1' s2 t,
               ~ s_low o s1 ->
               s_equiv o s1 s2 ->
               step s1 t s1' ->
               ~s_low o s1' ->
               s_equiv o s1' s2;

  highlowstep : forall o s1 s1' s2 s2' t1 t2,
                  s_equiv o s1 s2 ->
                  ~s_low o s1 ->
                  step s1 t1 s1' ->
                  s_low o s1' ->
                  step s2 t2 s2' ->
                  s_low o s2' ->
                  s_equiv o s1' s2'
}.

Section TINI.

Context {OS : ObservableSemantics}
        {UC : UnwindingSemantics}.

Definition trace := list event.

Inductive ti_trace_indist (o : observer) : relation trace :=
| titi_nil1: forall t2, ti_trace_indist o nil t2
| titi_nil2: forall t1, ti_trace_indist o t1 nil
| titi_cons : forall e1 e2 t1 t2,
    e_equiv o e1 e2 ->
    ti_trace_indist o t1 t2 ->
    ti_trace_indist o (e1 :: t1) (e2 :: t2).
Hint Constructors ti_trace_indist.

Let exec := @exec state event step.

Definition observe (o : observer) (es : list event) : list event :=
  filter (fun e => if e_low_dec o e then true else false) es.

Definition tini : Prop := forall o s1 t1 s1' s2 t2 s2',
                            s_equiv o s1 s2 ->
                            exec s1 t1 s1' ->
                            exec s2 t2 s2' ->
                            ti_trace_indist o (observe o t1) (observe o t2).

Lemma equiv_trace_high : forall o s1 e1 s1' s2 e2 s2'
                                (Hstep1 : step s1 e1 s1')
                                (Hstep2 : step s2 e2 s2')
                                (Hhigh1 : ~ s_low o s1)
                                (Heq : s_equiv o s1 s2),
                           e_equiv o e1 e2.
Proof.
  intros.
  assert (Hhigh2 : ~ s_low o s2) by (apply s_equiv_low in Heq; intuition).
  apply e_high_e_equiv;
  eauto using e_low_s_low.
Qed.

(* We define an alternative notion of execution ([oexec]) that is
similar to [exec], but removes invisible events. The difference is
that we merge consecutive high states in an execution together as a
single state, since the observer can't distinguish them
(c.f. [high_run] and [ostep] below). This allows us to keep two
equivalent executions in lockstep when inducting over one of them to
show NI. *)

Inductive high_run (o : observer) : state -> state -> Prop :=
| hr_refl : forall s, ~ s_low o s -> high_run o s s
| hr_step : forall s e s' s'',
              step s e s' ->
              ~ s_low o s ->
              high_run o s' s'' ->
              high_run o s s''.
Hint Constructors high_run.

Lemma high_run_high_l : forall o s s',
                          high_run o s s' ->
                          ~ s_low o s.
Proof. intros. inv H; eauto. Qed.

Lemma high_run_high_r : forall o s s',
                          high_run o s s' ->
                          ~ s_low o s'.
Proof. intros. induction H; eauto. Qed.

Inductive ostep (o : observer) : state -> event -> state -> Prop :=
| os_l : forall s e s',
           s_low o s ->
           step s e s' ->
           ostep o s e s'
| os_h : forall s s' e s'',
           high_run o s s' ->
           step s' e s'' ->
           s_low o s'' ->
           ostep o s e s''.
Hint Constructors ostep.

Lemma ostep_step : forall o s e s' e' s''
                          (Hstep : step s e s')
                          (Hlow : ~ s_low o s)
                          (Hlow' : ~ s_low o s')
                          (Hostep : ostep o s' e' s''),
                     ostep o s e' s''.
Proof.
  intros. inv Hostep; eauto.
  intuition.
Qed.
Hint Resolve ostep_step.

Inductive oexec (o : observer) : state -> trace -> state -> Prop :=
| oe_refl : forall s, oexec o s nil s
| oe_high_run : forall s s', high_run o s s' -> oexec o s nil s'
| oe_low : forall s e s' t s'',
             ostep o s e s' ->
             e_low o e ->
             oexec o s' t s'' ->
             oexec o s (e :: t) s''
| oe_high : forall s e s' t s'',
              ostep o s e s' ->
              ~ e_low o e ->
              oexec o s' t s'' ->
              oexec o s t s''.
Hint Constructors oexec.

Lemma oexec_low : forall o s e s' t s''
                         (Hstep : step s e s')
                         (Hlow : e_low o e)
                         (Hexec : oexec o s' t s''),
                   oexec o s (e :: t) s''.
Proof. intros. eauto using e_low_s_low. Qed.
Hint Resolve oexec_low.

Lemma oexec_high : forall o s e s' t s''
                          (Hstep : step s e s')
                          (Hhigh : ~ e_low o e)
                          (Hexec : oexec o s' t s''),
                    oexec o s t s''.
Proof.
  intros.
  destruct (s_low_dec o s);
  destruct (s_low_dec o s'); eauto.
  inv Hexec; eauto.
Qed.
Hint Resolve oexec_high.

Lemma exec_oexec : forall o s t s',
                     exec s t s' ->
                     oexec o s (observe o t) s'.
Proof.
  intros o s t s' H.
  unfold observe.
  induction H; simpl;
  try match goal with
        | e : event |- _ =>
          try destruct (e_low_dec o e); simpl
      end; eauto.
Qed.

Lemma high_run_s_equiv : forall o s1 s1' s2
                                (Hrun1 : high_run o s1 s1')
                                (Heq : s_equiv o s1 s2),
                           s_equiv o s1' s2.
Proof.
  intros.
  induction Hrun1; auto.
  apply IHHrun1.
  eapply highstep; auto.
  eapply H0.
  auto.
  eauto.
  eapply high_run_high_l; eauto.
Qed.

(* Two sequences of high states starting from equivalent states result
in equivalent states. *)

Lemma high_run_high_run : forall o s1 s1' s2 s2'
                                 (Hrun1 : high_run o s1 s1')
                                 (Hrun2 : high_run o s2 s2')
                                 (Heq : s_equiv o s1 s2),
                            s_equiv o s1' s2'.
Proof.
  intros.
  induction Hrun2 as [s2 Hhigh2
                     |s2 e2 s2' s2'' Hstep2 Hhigh2 Hrun2 IH].
  - eapply high_run_s_equiv; eauto.
  - eapply IH. clear IH.
    eapply s_equiv_sym.
    eapply highstep.
    eapply Hhigh2.
    eapply s_equiv_sym. auto.
    eauto.
    eapply high_run_high_l. eauto.
Qed.

(* The following lemma summarizes the previous unwinding conditions
stated in terms of [ostep], and corresponds to the inductive case when
proving NI for [oexec]. It says that if an observer observes a step
from two equivalent states (as defined in [ostep]), then the resulting
states and outputs are equivalent. *)

Lemma ostep_equiv : forall o s1 e1 s1' s2 e2 s2'
                           (Hstep1 : ostep o s1 e1 s1')
                           (Hstep2 : ostep o s2 e2 s2')
                           (Heq : s_equiv o s1 s2),
                      e_equiv o e1 e2 /\ s_equiv o s1' s2'.
Proof.
  intros.
  inversion Hstep1 as [? ? ? Hs1 Hstep1'|? s1'' ? ? Hhr1 Hstep1' Hs1']; subst. clear Hstep1.
  - assert (Hs2 : s_low o s2).
    {
      rewrite s_equiv_low; eauto.
      apply s_equiv_sym. trivial.
    }
    inversion Hstep2 as [? ? ? _ Hstep2'|? s2'' ? ? Hhr2 Hstep2' ?]; subst; clear Hstep2.
    + split.
      * eapply equiv_trace_low; eauto.
      * eapply lowstep; eauto.
    + apply high_run_high_l in Hhr2. intuition.
  - assert (Hs1 : ~ s_low o s1) by (eapply high_run_high_l; eauto).
    inversion Hstep2 as [? ? ? Hs2 Hstep2'|? s2'' ? ? Hhr2 Hstep2' ?]; subst; clear Hstep2.
    + rewrite <- s_equiv_low in Hs2; eauto. intuition.
    + assert (Heq'' : s_equiv o s1'' s2'') by (eapply high_run_high_run; eauto).
      apply high_run_high_r in Hhr1.
      clear Hhr2 Hs1 Heq Hstep1.
      split.
      * eapply equiv_trace_high; eauto.
      * eapply highlowstep; eauto.
Qed.

(* Noninterference in terms of [oexec] *)

Lemma oexec_equiv : forall o s1 t1 s1' s2 t2 s2'
                          (Hexec1 : oexec o s1 t1 s1')
                          (Hexec2 : oexec o s2 t2 s2')
                          (Heq : s_equiv o s1 s2),
                     ti_trace_indist o t1 t2.
Proof.
  intros.
  gdep t2. gdep s2.
  induction Hexec1;  eauto;
  intros s2 Heq t2 Hexec2;
  inv Hexec2; eauto;
  match goal with
    | Hstep1 : ostep _ ?s1 _ _,
      Hstep2 : ostep _ ?s2 _ _,
      Heq : s_equiv _ ?s1 ?s2 |- _ =>
      let H := fresh "H" in
      generalize (ostep_equiv Hstep1 Hstep2 Heq); intros H; destruct H
  end; simpl in *; eauto;
  match goal with
    | H : e_equiv _ _ _ |- _ =>
      apply e_equiv_low in H; intuition
  end.
Qed.

Theorem noninterference : tini.
Proof.
  intros o s1 t1 s1' s2 t2 s2' Heq Ht1 Ht2.
  eauto using exec_oexec, oexec_equiv.
Qed.

End TINI.
