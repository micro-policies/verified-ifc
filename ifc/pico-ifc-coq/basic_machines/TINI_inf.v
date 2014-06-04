(** The purpose of this file is to show that the definition in TINI.v
    adequately captures infinite executions, without explicitly
    talking about infinite objects. Intuitively, this is a consequence
    of TINI being a 2-safety hyperproperty.

    This file is not used by the rest of the Coq development. *)

Require Import List.
Require Import Relations.

Require Import Utils.
Require Import Semantics.
Require Import TINI.

Set Implicit Arguments.

Section CoExec.

Variable S : semantics.

Definition cotrace := colist (event S).

(* [next_event s1 e s2] says that an execution starting at state [s1]
remains silent until producing some output [e] and ending in state
[s2] *)

Inductive next_event : state S -> event S -> state S -> Prop :=
| ne_base : forall s e s'
                   (STEP : step S s (E e) s'),
              next_event s e s'
| ne_step : forall s s' e s''
                   (STEP : step S s Silent s')
                   (NEXT : next_event s' e s''),
              next_event s e s''.

(* [coexec] is similar to the definition of [exec] in [TINI.v], but
considers complete (potentially infinite) executions. [coexec s t]
states that a full execution starting at state [s] produces trace
[t]. *)

CoInductive coexec (s : state S) : cotrace -> Prop :=
| ce_end : forall (SILENT : forall e s', ~ next_event s e s'), coexec s Nil
| ce_step : forall e s' t
                   (NEXT : next_event s e s')
                   (EXEC : coexec s' t),
              coexec s (Cons e t).

End CoExec.

Section Observation.

Variable S : semantics.
Let coexec := @coexec S.
Let cotrace := @cotrace S.

Context (OE : Observation S).

(* [ti_cotrace_indist] is the coinductive version of [ti_trace_indist] *)

CoInductive ti_cotrace_indist : relation cotrace :=
| ticti_nil1 : forall t2, ti_cotrace_indist Nil t2
| ticti_nil2 : forall t1, ti_cotrace_indist t1 Nil
| ticti_cons : forall e t1 t2,
    ti_cotrace_indist t1 t2 ->
    ti_cotrace_indist (Cons e t1) (Cons e t2).
Hint Constructors ti_cotrace_indist.

(* [contains P t l e t'] expresses that we can decompose [t = l ++ e
:: t'], where [l] is a finite list, such that [P] holds of [e] but
doesn't hold of any element of [l] *)

Inductive contains T (P : T -> Prop)
    : colist T -> T -> list T -> colist T -> Prop :=
  | c_found : forall e t,
      P e ->
      contains P (Cons e t) e nil t
  | c_later : forall e e' t t' l,
      ~(P e) ->
      contains P t e' l t' ->
      contains P (Cons e t) e' (e :: l) t'.

Hint Constructors contains.

(* Because of the guard conditions for cofixpoints, we must define
filter on infinite lists as a predicate. [colist_filter P t1 t2]
states that [t2] is obtained from [t1] by removing the elements that
don't satisfy [P] *)

CoInductive colist_filter T (P : T -> Prop) : colist T -> colist T -> Prop :=
| f_not_contains : forall t,
    (forall e t' l, ~contains P t e l t') ->
    colist_filter P t Nil
| f_contains : forall e t t' t'' l,
    contains P t e l t' ->
    colist_filter P t' t'' ->
    colist_filter P t (Cons e t'').

(* We can now use this filtering predicate to define what the
observation of a complete trace is *)

Definition coobserve o es es' := colist_filter (e_low o) es es'.

(* The definition of TINI for this setting is similar to the finite
case, but we state the observation of traces in terms of a predicate
instead of a function *)

Definition cotini : Prop := forall o i t t' i2 t2 t2',
  i_equiv o i i2 ->
  coexec (init_state _ i) t ->
  coexec (init_state _ i2) t2 ->
  coobserve o t t' ->
  coobserve o t2 t2' ->
  ti_cotrace_indist t' t2'.

(* In order to prove cotrace indistinguishability it
   suffices to prove it for all finite prefixes *)
Lemma ti_cotrace_indist_via_prefixes : forall (t t2 : cotrace),
  (forall p p2, list_prefix_colist p t ->
                list_prefix_colist p2 t2 ->
                ti_trace_indist p p2) ->
  ti_cotrace_indist t t2.
Proof. cofix. intros.
  destruct t; destruct t2. eauto. eauto. eauto.
  - assert (J : ti_trace_indist (e :: nil) (e0 :: nil)) by (apply H; eauto).
    inv J.
    apply ticti_cons; auto.
    apply ti_cotrace_indist_via_prefixes; auto.
    intros.
    assert (G : ti_trace_indist (e0 :: p) (e0 :: p2)); auto.
    inv G. auto.
Qed.

(* We now prove some technical lemmas needed to relate finite prefixes
to the infinite notions we've defined *)

Lemma contains_prefix : forall T l P t (e : T) t' p,
  contains P t e l t' ->
  list_prefix_colist p t' ->
  list_prefix_colist (l ++ e :: p) t.
Proof. induction l; simpl; intros; inv H; eauto. Qed.

Lemma contains_P_e : forall T l P t (e : T) t',
  contains P t e l t' ->
  P e.
Proof. induction 1; eauto. Qed.

Lemma contains_filter_P_l :
  forall T (P : T -> Prop) (P_dec : forall e, {P e} + {~P e}),
  forall l t (e : T) t',
  contains P t e l t' ->
  filter (fun e0 => if P_dec e0 then true else false) l = nil.
Proof. induction 1; simpl. reflexivity. rewrite if_dec_right; eauto. Qed.

Lemma prefix_cofilter :
  forall (P : event S -> Prop) (P_dec : forall e, {P e} + {~P e}),
  forall p' t' t,
  list_prefix_colist p' t' ->
  colist_filter P t t' ->
  exists p, list_prefix_colist p t /\
  filter (fun e => if P_dec e then true else false) p = p'.
Proof.
  intros P P_dec p' t' t H. gdep t. induction H; intros t H0.
  - exists nil; eauto.
  - inv H0.
    destruct (IHlist_prefix_colist _ H5) as [p [? ?]].
    eexists (l0 ++  e :: p). split. eauto using contains_prefix.
    rewrite filter_app. simpl. rewrite if_dec_left. rewrite H1.
    erewrite contains_filter_P_l; [reflexivity | eassumption].
    eapply contains_P_e. eassumption.
Qed.

Hint Constructors exec.
Lemma next_event_exec :
  forall s e s' t s''
         (NEXT : next_event S s e s')
         (EXEC : exec s' t s''),
    exec s (e :: t) s''.
Proof. induction 1; intros; eauto. Qed.


Lemma prefix_coexec :  forall p t s,
  list_prefix_colist p t ->
  coexec s t ->
  exists s'', exec s p s''.
Proof.
  intros. gdep s. induction H; intros s EXEC. eauto using e_refl.
  inv EXEC. destruct (IHlist_prefix_colist _ EXEC0) as [s'' EXEC].
  eauto using next_event_exec.
Qed.

(* Now, we are able to prove our main result *)

Theorem tini_cotini : tini OE -> cotini.
Proof.
  unfold tini, cotini.
  intros Htini o i1 t1 t1' i2 t2 t2' Hi Hexec1 Hexec2 Hobs1 Hobs2.
  apply ti_cotrace_indist_via_prefixes. intros p1' p2' Hpre1' Hpre2'.
  destruct (prefix_cofilter (e_low_dec o) Hpre1' Hobs1) as [p1 [Hpre1 Hfil1]].
  destruct (prefix_cofilter (e_low_dec o) Hpre2' Hobs2) as [p2 [Hpre2 Hfil2]].
  destruct (prefix_coexec Hpre1 Hexec1).
  destruct (prefix_coexec Hpre2 Hexec2).
  subst. unfold observe in Htini.
  eapply Htini ; eauto.
Qed.

End Observation.
