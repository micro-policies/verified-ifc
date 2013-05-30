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
Require Import BackwardCommon.

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

Hint Constructors match_stacks.

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
