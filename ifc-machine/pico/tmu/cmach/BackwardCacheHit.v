Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import WfCLattices.
Require Import TMUInstr.
Require Import Abstract.
Require Import AbstractCommon.
Require Import Rules.
Require Import QuasiAbstractMachine.
Require Import Concrete.
Require Import ConcreteMachineSmallStep.
Require Import Determinism.
Require Import Refinement.

Open Scope Z_scope.

Set Implicit Arguments.

Section CacheHitSimulation.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {WFCLatt: WfConcreteLattice L Latt CLatt}.

Definition abstract_event (ce : option CEvent) : option (@Event L) :=
  match ce with
    | Some (CEInt ca) => Some (EInt (atom_ZToLab ca))
    | None => None
  end.

Lemma read_m_labToZ' :
  forall i m xv xl,
    read_m i (mem_labToZ m) = Some (xv, xl) ->
    exists xl',
      read_m i m = Some (xv, xl') /\
      xl = labToZ xl'.
Proof.
  unfold index_list_Z.
  intros.
  destruct (i <? 0). inv H.
  gdep m.
  generalize (Z.to_nat i). clear i.
  intros i.
  induction i as [|i IH];
  intros m H;
  destruct m as [|[xv' xl'] m'];
  simpl in *; inv H; intuition.
  eexists. split; repeat f_equal.
Qed.

(* Reconstruct the quasi-abstract label vector *)
Ltac quasi_abstract_labels :=
  match goal with
    | H : cache_hit _ _ (dontCare, dontCare, dontCare) _ |- _ =>
      pose (vls := Vector.nil L)
    | H : cache_hit _ _ (labToZ ?l, dontCare, dontCare) _ |- _ =>
      pose (vls := Vector.cons _ l _ (Vector.nil _))
    | H : cache_hit _ _ (labToZ ?l1, labToZ ?l2, dontCare) _ |- _ =>
      pose (vls := Vector.cons _ l1 _ (Vector.cons _ l2 _ (Vector.nil _)))
    | H : cache_hit _ _ (labToZ ?l1, labToZ ?l2, labToZ ?l3) _ |- _ =>
      pose (vls := Vector.cons _ l1 _
                               (Vector.cons _ l2 _
                                            (Vector.cons _ l3 _ (Vector.nil _))))
  end.

(* Borrowed from CPDT *)
(* Instantiate a quantifier in a hypothesis [H] with value [v], or,
if [v] doesn't have the right type, with a new unification variable.
Also prove the lefthand sides of any implications that this exposes,
simplifying [H] to leave out those implications. *)

Ltac guess v H :=
 repeat match type of H with
          | forall x : ?T, _ =>
            match type of T with
              | Prop =>
                (let H' := fresh "H'" in
                  assert (H' : T); [
                    solve [ eauto 6 ]
                    | specialize (H H'); clear H' ])
                || fail 1
              | _ =>
                specialize (H v)
                || let x := fresh "x" in
                  evar (x : T);
                  let x' := eval unfold x in x in
                    clear x; specialize (H x')
            end
        end.

(* Relate the results of a cache read to its arguments *)
Ltac analyze_cache_hit OP vls apcl:=
  match goal with
    | CACHE : cache_up2date _ |- _ =>
      let H := fresh "H" in
      generalize (@CACHE OP vls apcl);
      intros H; guess tt H;
      unfold apply_rule in H; simpl in H;
      guess tt H; simpl in H;
      try match type of H with
            | exists _, _ =>
              destruct H as [? ?]
          end;
      try match type of H with
            | context[if ?b then _ else _] =>
              destruct b eqn:Hb
          end;
      intuition;
      match goal with
        | H1 : cache_hit_read _ _ _,
          H2 : cache_hit_read _ _ _ |- _ =>
          let H := fresh "H" in
          generalize (cache_hit_read_determ H1 H2);
          intros H;
          destruct H;
          subst;
          clear H2
      end
  end.

Lemma match_stacks_args' : forall s args cs,
                             match_stacks s (args ++ cs) ->
                             exists args' s',
                               s = args' ++ s' /\ match_stacks args' args /\ match_stacks s' cs.
Proof.
Hint Constructors match_stacks.
  intros s args. gdep s.
  induction args; intros.
  simpl in *. exists nil; exists s. split; auto.
  inv H;
    (exploit IHargs; eauto; intros [args' [cs' [Heq [Hmatch Hmatch']]]]);
    (inv Heq; (eexists; eexists; split; eauto ; try reflexivity)).
Qed.

Lemma match_stacks_data' : forall s cs,
                              match_stacks s cs ->
                              (forall a : CStkElmt, In a cs -> exists d : Atom, a = CData d) ->
                              (forall a : StkElmt, In a s -> exists d : Atom, a = AData d).
Proof.
  induction 1;  intros.
  - inv H0.
  - inv H2.  eauto.
    eapply IHmatch_stacks; eauto.
    intros; eapply H1; eauto.
    econstructor 2; eauto.
  - inv H2.
    eelim (H1 (CRet (atom_labToZ a) r false)); eauto. intros. inv H0.
    constructor; auto.
    eapply IHmatch_stacks; eauto.
    intros; eapply H1; eauto.
    econstructor 2; eauto.
Qed.

Hint Constructors pop_to_return.

Lemma match_stacks_c_pop_to_return :
  forall astk cstk rpc rpcl b1 b2 cstk'
         (MATCH : match_stacks astk cstk)
         (POP : c_pop_to_return cstk (CRet (rpc, rpcl) b1 b2 :: cstk')),
    exists rpcl' astk',
      pop_to_return astk (ARet (rpc, rpcl') b1 :: astk') /\
      rpcl = labToZ rpcl' /\
      match_stacks astk' cstk'.
Proof.
  intros.
  gdep astk.
  match type of POP with
    | c_pop_to_return _ ?CSTK =>
      remember CSTK as cstk''
  end.
  induction POP; subst;
  intros astk MATCH; inv MATCH; try inv Heqcstk''; eauto;
  repeat match goal with
           | A : Atom |- _ => destruct A; simpl in *
           | H : (_, _) = (_, _) |- _ => inv H; simpl in *
         end;
  eauto.
  guess tt IHPOP.
  destruct IHPOP as [? [? [? [? ?]]]].
  subst. eauto 7.
Qed.
Hint Resolve match_stacks_c_pop_to_return.

Lemma upd_m_labToZ : forall i xv xl m cm'
                            (UP : upd_m i (xv, labToZ xl) (mem_labToZ m) = Some cm'),
                       exists m',
                         upd_m i (xv, xl) m = Some m' /\
                         cm' = mem_labToZ m'.
Proof.
  intros i; unfold upd_m; intros.
  destruct (i <? 0). inv UP.
  gdep cm'. gdep m.
  generalize (Z.to_nat i). clear i.
  intros i.
  induction i as [|i IH];
  intros [| [xv' xl']] cm' UP; simpl in *; inv UP.
  repeat eexists.
  destruct (update_list i (xv, labToZ xl) (mem_labToZ l)) eqn:E; inv H0.
  guess tt IH.
  destruct IH. intuition.
  subst. eexists. rewrite H0.
  eauto.
Qed.

Ltac try_exploit l :=
  try (exploit l;
       try solve [eauto];
       let H := fresh "H" in intros H;
       repeat match goal with
                | [H : (exists _, _) |- _ ] => destruct H
                | [H : _ /\ _ |- _ ] => destruct H
              end;
       subst).

Lemma cache_hit_simulation :
  forall s1 s2 e s2'
         (Hmatch : match_states s1 s2)
         (Hs2' : priv s2' = false)
         (Hstep : cstep s2 e s2'),
    exists s1', step_rules s1 (abstract_event e) s1' /\
                match_states s1' s2'.
Proof.
  intros.
  inv Hmatch.
  destruct apc as [apc apcl].
  inv Hstep; simpl in *; try congruence;

  (* Invert some hypotheses *)
  repeat match goal with
           | H : ?x = ?x |- _ => clear H
           | H : match_stacks _ (_ ::: _) |- _ => inv H
           | H : match_stacks _ (_ ++ _) |- _ =>
             apply match_stacks_args' in H;
             destruct H as [? [? [? [? ?]]]];
             subst
           | a : _,
             H : (_, _) = atom_labToZ ?a |- _ =>
             destruct a; simpl in H; inv H
         end;

  (* For the Load case *)
  try_exploit read_m_labToZ';

  (* For the Ret cases *)
  try_exploit match_stacks_c_pop_to_return;

  quasi_abstract_labels;

  (* Find the current opcode *)
  match goal with
    | H : read_m _ _ = Some ?instr |- _ =>
      let opcode := (eval compute in (opcode_of_instr instr)) in
      match opcode with
        | Some ?opcode => pose (OP := opcode)
      end
  end;

  analyze_cache_hit OP vls apcl;

  subst OP vls;

  (* For the Store case *)
  try_exploit upd_m_labToZ;

  (* For the BranchNZ case *)
  try match goal with
        | |- context[if (?z =? 0) then _ else _ ] =>
          let H := fresh "H" in
          assert (H := Z.eqb_spec z 0);
          destruct (z =? 0);
          inv H
      end;

  try solve [
        eexists; split;
        try (econstructor (solve [compute; eauto]));
        repeat (constructor; eauto); simpl; f_equal; intuition
      ].

  - eexists; split.
    eapply step_store; eauto.
    + unfold run_tmr, apply_rule.
      simpl.
      rewrite Hb. eauto.
    + constructor; eauto.

  - eexists; split.
    + eapply step_call; try solve [compute; eauto].
      * erewrite match_stacks_length; eauto.
      * eapply match_stacks_data'; eauto.
    + repeat (constructor; eauto); simpl; f_equal; intuition.
      eauto using match_stacks_app.

  - eexists; split.
    constructor; eauto.
    + rewrite <- ZToLab_labToZ_id. reflexivity.
    + constructor; eauto.
Qed.

End CacheHitSimulation.
