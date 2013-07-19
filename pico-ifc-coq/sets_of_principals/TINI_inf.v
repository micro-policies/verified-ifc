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

Inductive next_event : state S -> event S -> state S -> Prop :=
| ne_base : forall s e s'
                   (STEP : step S s (E e) s'),
              next_event s e s'
| ne_step : forall s s' e s''
                   (STEP : step S s Silent s')
                   (NEXT : next_event s' e s''),
              next_event s e s''.

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

Context (e_obs : Type) (OE : Observation S e_obs).

CoInductive ti_cotrace_indist (o : @observer _ _ OE) : relation cotrace :=
| ticti_nil1 : forall t2, ti_cotrace_indist o Nil t2
| ticti_nil2 : forall t1, ti_cotrace_indist o t1 Nil
| ticti_cons : forall e1 e2 t1 t2,
    out e1 = out e2 ->             
    ti_cotrace_indist o t1 t2 ->
    ti_cotrace_indist o (Cons e1 t1) (Cons e2 t2).
Hint Constructors ti_cotrace_indist.

(* TODO: move this to Utils.v? *)
(* XXX: This doesn't work well in proofs; replaced by definition below *)
CoInductive colist_filter (A : Type) (P : A -> Prop)
  : colist A -> colist A -> Prop :=
| cf_nil : colist_filter P Nil Nil
| cf_cons_P : forall e t t',
    P e ->
    colist_filter P t t' ->
    colist_filter P (Cons e t) (Cons e t')
| cf_cons_not_P : forall e t t',
    ~P e ->
    colist_filter P t t' ->
    colist_filter P (Cons e t) t'.

(* XXX: This works well for the proof we need here *)
(* TODO: relate this to the definition above? *)
(* TODO: move this to Utils.v? *)
(* TODO: find better name: first element satisfying P? break up? *)
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

CoInductive colist_filter' T (P : T -> Prop) : colist T -> colist T -> Prop :=
| f_not_contains : forall t,
    (forall e t' l, ~contains P t e l t') ->
    colist_filter' P t Nil
| f_contains : forall e t t' t'' l,
    contains P t e l t' ->
    colist_filter' P t' t'' ->
    colist_filter' P t (Cons e t'').

Definition coobserve o es es' := colist_filter' (fun e => e_low o (out e)) es es'.

Definition cotini : Prop := forall o i t t' i2 t2 t2',
  i_equiv o i i2 ->
  coexec (init_state _ i) t ->
  coexec (init_state _ i2) t2 ->
  coobserve o t t' ->
  coobserve o t2 t2' ->
  ti_cotrace_indist o t' t2'.

(* In order to prove cotrace indistinguishability it
   suffices to prove it for all finite prefixes *)
Lemma ti_cotrace_indist_via_prefixes : forall o (t t2 : cotrace),
  (forall p p2, list_prefix_colist p t ->
                list_prefix_colist p2 t2 ->
                ti_trace_indist (map (out (S:=S)) p) (map (out (S:=S)) p2)) ->
  ti_cotrace_indist o t t2.
Proof. cofix. intros.
  destruct t; destruct t2. eauto. eauto. eauto.
  - assert (J : ti_trace_indist (out e :: nil) (out e0 :: nil)) by (apply (H (e::nil) (e0::nil)); eauto).
    inv J.
    apply ticti_cons; auto.
    apply ti_cotrace_indist_via_prefixes; auto.
    intros.
    assert (G : ti_trace_indist (map (out (S:=S)) (e :: p)) (map (out (S:=S)) (e0 :: p2)))
    by auto.
    inv G. auto.
Qed.

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

Lemma prefix_cofilter' :
  forall (P : event S -> Prop) (P_dec : forall e, {P e} + {~P e}),
  forall p' t' t,
  list_prefix_colist p' t' ->
  colist_filter' P t t' ->
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

Theorem tini_cotini : tini OE -> cotini.
Proof.
  unfold tini, cotini.
  intros Htini o i1 t1 t1' i2 t2 t2' Hi Hexec1 Hexec2 Hobs1 Hobs2.
  apply ti_cotrace_indist_via_prefixes. intros p1' p2' Hpre1' Hpre2'.
  destruct (prefix_cofilter' (fun e => e_low_dec o (out e)) Hpre1' Hobs1) as [p1 [Hpre1 Hfil1]].
  destruct (prefix_cofilter' (fun e => e_low_dec o (out e)) Hpre2' Hobs2) as [p2 [Hpre2 Hfil2]].
  destruct (prefix_coexec Hpre1 Hexec1).
  destruct (prefix_coexec Hpre2 Hexec2).
  subst. unfold observe in Htini.
  eapply Htini; eauto.
Qed.

End Observation.
