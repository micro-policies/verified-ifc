Require Import RelationClasses.
Require Import Relations.
Require Import List.
Require Import Utils.
Require Import Semantics.

(** Termination-Insensitive Non-Interference (TINI). 
    Also includes some basic definitions about execution and
    observations for a semantics. *)

Set Implicit Arguments.

Section Exec.

Variable S : semantics.

Definition trace := list (event S).

Inductive exec : state S -> trace -> state S -> Prop :=
| e_refl : forall s, exec s nil s
| e_event_step : forall s e s' t s'',
             step S s (E e) s' ->
             exec s' t s'' ->
             exec s (e :: t) s''
| e_silent_step : forall s s' t s'',
             step S s Silent s' ->
             exec s' t s'' ->
             exec s t s''.

End Exec.

Section OBSERVATION.

Variable S: semantics.
Let exec := @exec S.
Let trace := @trace S.

Class Observation := {
  observer : Type;
  e_low : observer -> (event S) -> Prop;
  e_low_dec : forall o e, {e_low o e} + {~ e_low o e};
  i_equiv : observer -> relation (init_data S)
}. 

Section TINI.

Context (OE : Observation).

Inductive ti_trace_indist : relation trace :=
| titi_nil1: forall t2, ti_trace_indist nil t2
| titi_nil2: forall t1, ti_trace_indist t1 nil
| titi_cons : forall e t1 t2,
    ti_trace_indist t1 t2 ->
    ti_trace_indist (e :: t1) (e :: t2).
Hint Constructors ti_trace_indist.

Definition observe (o : observer) (es : trace) : trace :=
  filter (fun e => if e_low_dec o e then true else false) es.

Lemma observe_forall : forall o es, Forall (e_low o) (observe o es).
Proof.
  induction es as [|e es IH]; simpl.
  - constructor.
  - destruct (e_low_dec o e); auto.
Qed.

Definition tini : Prop := forall o i1 t1 s1 i2 t2 s2,
                            i_equiv o i1 i2 ->
                            exec (init_state _ i1) t1 s1 ->
                            exec (init_state _ i2) t2 s2 ->
                            ti_trace_indist (observe o t1) (observe o t2).

Definition a_low (o:observer) (a:(event S)+τ) : Prop :=
  match a with
    | Silent => False
    | E e => e_low o e
  end.

Inductive a_equiv (o : observer) : relation ((event S)+τ) :=
| ee_low : forall a, a_equiv o a a 
| ee_high : forall a1 a2, ~ a_low o a1 ->
                          ~ a_low o a2 ->
                          a_equiv o a1 a2.
Hint Constructors a_equiv.

Global Instance a_equiv_equiv (o: observer) : @Equivalence _ (a_equiv o).
Proof.
  constructor.
  - intros e. auto.
  - intros x y Hxy. inv Hxy ; auto.
  - intros x y z Hxy Hyz. inv Hxy; inv Hyz; auto.
Qed.

Class UnwindingSemantics := {
  s_equiv : observer -> relation (state S);
  i_equiv_s_equiv : forall o i1 i2,
                      i_equiv o i1 i2 ->
                      s_equiv o (init_state _ i1) (init_state _ i2);
  s_low : observer -> (state S) -> Prop;
  s_low_dec : forall o s, {s_low o s} + {~ s_low o s};
  s_equiv_sym : forall o, symmetric _ (s_equiv o);
  s_equiv_low : forall o s1 s2, s_equiv o s1 s2 -> (s_low o s1 <-> s_low o s2);

  e_low_s_low : forall o s1 e s2,
                  step S s1 (E e) s2 ->
                  e_low o e ->
                  s_low o s1;

  (* Unwinding conditions *)

  equiv_trace_low: forall o s1 s2 a1 a2 s1' s2',
                     s_equiv o s1 s2 ->
                     s_low o s1 ->
                     step S s1 a1 s1' ->
                     step S s2 a2 s2' ->
                     a_equiv o a1 a2;

  lowstep : forall o a1 a2 s1 s1' s2 s2',
              s_equiv o s1 s2 ->
              s_low o s1 ->
              step S s1 a1 s1' ->
              step S s2 a2 s2' ->
              s_equiv o s1' s2';

  highstep : forall o s1 s1' s2 a,
               ~ s_low o s1 ->
               s_equiv o s1 s2 ->
               step S s1 a s1' ->
               ~s_low o s1' ->
               s_equiv o s1' s2;

  highlowstep : forall o s1 s1' s2 s2' a1 a2,
                  s_equiv o s1 s2 ->
                  ~s_low o s1 ->
                  step S s1 a1 s1' ->
                  s_low o s1' ->
                  step S s2 a2 s2' ->
                  s_low o s2' ->
                  s_equiv o s1' s2'
}.

Section TINIUnwinding.

Context {UC : UnwindingSemantics}.

Lemma equiv_trace_high : forall o s1 e1 s1' s2 e2 s2'
                                (Hstep1 : step S s1 e1 s1')
                                (Hstep2 : step S s2 e2 s2')
                                (Hhigh1 : ~ s_low o s1)
                                (Heq : s_equiv o s1 s2),
                           a_equiv o e1 e2.
Proof.
  intros.
  assert (Hhigh2 : ~ s_low o s2) by (apply s_equiv_low in Heq; intuition).
  destruct e1; destruct e2;
  constructor; eauto using e_low_s_low.
Qed.

(** We define an alternative notion of execution ([oexec]) that is
similar to [exec], but removes invisible events. The difference is
that we merge consecutive high states in an execution together as a
single state, since the observer can't distinguish them
(c.f. [high_run] and [ostep] below). This allows us to keep two
equivalent executions in lockstep when inducting over one of them to
show NI. *)

Inductive high_run (o : observer) : state S -> state S -> Prop :=
| hr_refl : forall s, ~ s_low o s -> high_run o s s
| hr_step : forall s e s' s'',
              step S s e s' ->
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

Inductive ostep (o : observer) : state S -> (event S)+τ -> state S -> Prop :=
| os_l : forall s a s',
           s_low o s ->
           step S s a s' ->
           ostep o s a s'
| os_h : forall s s' a s'',
           high_run o s s' ->
           step S s' a s'' ->
           s_low o s'' ->
           ostep o s a s''.
Hint Constructors ostep.

Lemma ostep_step : forall o s a s' a' s''
                          (Hstep : step S s a s')
                          (Hlow : ~ s_low o s)
                          (Hlow' : ~ s_low o s')
                          (Hostep : ostep o s' a' s''),
                     ostep o s a' s''.
Proof.
  intros. inv Hostep; eauto.
  intuition.
Qed.
Hint Resolve ostep_step.

Inductive oexec (o : observer) : state S -> trace -> state S -> Prop :=
| oe_refl : forall s, oexec o s nil s
| oe_high_run : forall s s', high_run o s s' -> oexec o s nil s'
| oe_low : forall s e s' t s'',
             ostep o s (E e) s' ->
             e_low o e ->
             oexec o s' t s'' ->
             oexec o s (e :: t) s''
| oe_high : forall s e s' t s'',
              ostep o s (E e) s' ->
              ~ e_low o e ->
              oexec o s' t s'' ->
              oexec o s t s''
| oe_silent : forall s s' t s'',
              ostep o s Silent s' ->
              oexec o s' t s'' ->
              oexec o s t s''.
Hint Constructors oexec.

Lemma oexec_low : forall o s e s' t s''
                         (Hstep : step S s (E e) s')
                         (Hlow : e_low o e)
                         (Hexec : oexec o s' t s''),
                   oexec o s (e :: t) s''.
Proof. intros. eauto using e_low_s_low. Qed.
Hint Resolve oexec_low.

Lemma oexec_high : forall o s e s' t s''
                          (Hstep : step S s (E e) s')
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

Lemma oexec_silent : forall o s s' t s''
                          (Hstep : step S s Silent s')
                          (Hexec : oexec o s' t s''),
                    oexec o s t s''.
Proof.
  intros.
  destruct (s_low_dec o s);
  destruct (s_low_dec o s'); eauto.
  inv Hexec; eauto.
Qed.
Hint Resolve oexec_silent.

Lemma exec_oexec : forall o s t s',
                     exec s t s' ->
                     oexec o s (observe o t) s'.
Proof.
  intros o s t s' H.
  unfold observe.
  induction H; simpl;
  try match goal with
        | e : event S |- _ =>
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

(** Two sequences of high states starting from equivalent states result
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

(** The following lemma summarizes the previous unwinding conditions
stated in terms of [ostep], and corresponds to the inductive case when
proving NI for [oexec]. It says that if an observer observes a step
from two equivalent states (as defined in [ostep]), then the resulting
states and outputs are equivalent. *)

Lemma ostep_equiv : forall o s1 a1 s1' s2 a2 s2'
                           (Hstep1 : ostep o s1 a1 s1')
                           (Hstep2 : ostep o s2 a2 s2')
                           (Heq : s_equiv o s1 s2),
                      a_equiv o a1 a2 /\ s_equiv o s1' s2'.
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

(** Noninterference in terms of [oexec] *)

Lemma oexec_equiv : forall o s1 t1 s1' s2 t2 s2'
                          (Hexec1 : oexec o s1 t1 s1')
                          (Hexec2 : oexec o s2 t2 s2')
                          (Heq : s_equiv o s1 s2),
                     ti_trace_indist t1 t2.
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
    | H : a_equiv _ _ _ |- _ =>
      inv H; intuition; eauto
  end.
Qed.

Theorem noninterference : tini.
Proof.
  intros o s1 t1 s1' s2 t2 s2' Heq Ht1 Ht2.
  eauto using i_equiv_s_equiv, exec_oexec, oexec_equiv.
Qed.

End TINIUnwinding.

End TINI.

End OBSERVATION.
