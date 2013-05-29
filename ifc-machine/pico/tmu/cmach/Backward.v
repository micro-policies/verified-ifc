Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import WfCLattices.
Require Import TMUInstr.
Require Import Abstract.
Require Import Rules.
Require Import QuasiAbstractMachine.
Require Import Concrete.
Require Import ConcreteMachineSmallStep.
Require Import Determinism.
Require Import Refinement.
Require TINI.

Open Scope Z_scope.

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

Section Simulation.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {WFCLatt: WfConcreteLattice L Latt CLatt}.

Definition abstract_event (ce : option CEvent) : option (@Event L) :=
  match ce with
    | Some (CEInt ca) => Some (EInt (atom_ZToLab ca))
    | None => None
  end.

(* FIXME: Move this somewhere else *)
Definition opcode_of_instr (i : Instr) : option OpCode :=
  match i with
    | Noop => Some OpNoop
    | Add => Some OpAdd
    | Sub => Some OpSub
    | Push _ => Some OpPush
    | Load => Some OpLoad
    | Store => Some OpStore
    | Jump => Some OpJump
    | BranchNZ _ => Some OpBranchNZ
    | Call _ _ => Some OpCall
    | Ret => Some OpRet
    | VRet => Some OpVRet
    | Halt => None
    | Output => Some OpOutput
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

(* FIXME: Move this somewhere else *)
Ltac intro_if_new k :=
  match goal with
    | H : ?P |- ?P -> _ => fail 1
    | |- _ => k
  end.

(* Reconstruct the quasi-abstract label vector *)
Ltac quasi_abstract_labels :=
  try match goal with
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
  inv Hstep; simpl in *;

  (* Invert some hypotheses *)
  repeat match goal with
           | H : true = false |- _ => inv H
           | H : ?x = ?x |- _ => clear H
           | H : match_stacks _ (_ ::: _) |- _ => inv H
           | a : _,
             H : (_, _) = atom_labToZ ?a |- _ =>
             destruct a; simpl in H; inv H
         end;

  try match goal with
        | H : read_m _ _ = Some _ |- _ =>
          let H' := fresh "H'" in
          exploit read_m_labToZ'; eauto;
          intro_if_new ltac:(
            intros H' ; destruct H' as [? [? ?]]; subst
          )
      end;

  quasi_abstract_labels;

  (* Find the current opcode *)
  match goal with
    | H : read_m _ _ = Some ?instr |- _ =>
      let opcode := (eval compute in (opcode_of_instr instr)) in
      match opcode with
        | Some ?opcode => pose (OP := opcode)
      end
  end;

  try (exploit (@CACHE OP vls apcl _ apcl eq_refl); eauto;
       let H := fresh "H" in
       intros H;
       repeat match goal with
                | H : exists t, _ |- _ =>
                  destruct H as [t' H]
              end;

       match goal with
         | H1 : cache_hit_read _ _ _,
                H2 : cache_hit_read _ _ _ |- _ =>
           let H := fresh "H" in
           generalize (cache_hit_read_determ H1 H2); intros H
       end);

  try solve [
        eexists; split;
        try (econstructor (solve [compute; eauto]));
        repeat (constructor; eauto); simpl; f_equal; intuition
      ].

Admitted.

End Simulation.

End Backward.
