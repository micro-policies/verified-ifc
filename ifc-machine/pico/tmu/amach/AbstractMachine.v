Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.

Require Import TMUInstr.
Require Import Abstract.
Require Import AbstractCommon.

Set Implicit Arguments.

Local Open Scope Z_scope.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Inductive step_rules : @AS T -> option (@Event T) -> @AS T -> Prop :=
| step_nop : forall m i s pcv pcl,
    index_list_Z pcv i = Some Noop ->
    step_rules (AState m i s (pcv,pcl)) None (AState m i s (pcv+1,pcl))

| step_add: forall m i s pcv pcl x1v x1l x2v x2l,
    index_list_Z pcv i = Some Add ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               None
               (AState m i ((AData (x1v+x2v,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_sub: forall m i s pcv pcl x1v x1l x2v x2l,
    index_list_Z pcv i = Some Sub ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               None
               (AState m i ((AData (x1v-x2v,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_push: forall m i s pcv pcl cv,
    index_list_Z pcv i = Some (Push cv) ->
    step_rules (AState m i s (pcv,pcl))
               None
               (AState m i ((AData (cv,bot))::s) (pcv+1,pcl))

| step_load: forall m i s pcv pcl addrv addrl xv xl,
    index_list_Z pcv i = Some Load ->
    index_list_Z addrv m = Some (xv,xl) ->
    step_rules (AState m i ((AData (addrv,addrl))::s) (pcv,pcl))
               None
               (AState m i ((AData (xv,addrl \_/ xl)::s)) (pcv+1,pcl))

| step_store: forall m i s pcv pcl addrv addrl xv xl mv ml m',
    index_list_Z pcv i = Some Store ->
    index_list_Z addrv m = Some (mv,ml) ->
    addrl \_/ pcl <: ml = true ->
    update_list_Z addrv (xv, addrl \_/ (xl \_/ pcl)) m = Some m' ->
    step_rules (AState m i ((AData (addrv,addrl))::(AData (xv,xl))::s) (pcv,pcl))
               None
               (AState m' i s (pcv+1,pcl))

| step_jump: forall m i s pcv pcl pcv' pcl',
    index_list_Z pcv i = Some Jump ->
    step_rules (AState m i ((AData (pcv',pcl'))::s) (pcv,pcl))
               None
               (AState m i s (pcv',pcl' \_/ pcl))

| step_branchnz_true: forall m i s pcv pcl offv al,
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    step_rules (AState m i ((AData (0,al))::s) (pcv,pcl))
               None
               (AState m i s (pcv+1,al \_/ pcl))

| step_branchnz_false: forall m i s pcv pcl offv av al,
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    av <> 0 ->
    step_rules (AState m i ((AData (av,al))::s) (pcv,pcl))
               None
               (AState m i s (pcv+offv,al \_/ pcl))

| step_call: forall m i s pcv pcl pcv' pcl' args a r,
    index_list_Z pcv i = Some (Call a r) ->
    length args = a ->
    (forall a, In a args -> exists d, a = AData d) ->
    step_rules (AState m i ((AData (pcv',pcl'))::args++s) (pcv,pcl))
               None
               (AState m i (args++(ARet (pcv+1,pcl) r)::s) (pcv',pcl' \_/ pcl))

| step_ret: forall m i s pcv pcl pcv' pcl' s' ,
    index_list_Z pcv i = Some Ret ->
    pop_to_return s ((ARet (pcv',pcl') false)::s') ->
    step_rules (AState m i s (pcv,pcl)) None (AState m i s' (pcv',pcl'))

| step_vret: forall m i s pcv pcl pcv' pcl' resv resl s' ,
    index_list_Z pcv i = Some VRet ->
    pop_to_return s ((ARet (pcv',pcl') true)::s') ->
    step_rules (AState m i (AData (resv,resl)::s) (pcv,pcl))
               None (AState m i (AData (resv, resl \_/ pcl)::s') (pcv',pcl'))

| step_output: forall m i s pcv pcl xv xl,
    index_list_Z pcv i = Some Output ->
    step_rules (AState m i (AData (xv,xl)::s) (pcv,pcl))
               (Some (EInt (xv,xl \_/ pcl))) (AState m i s (pcv+1,pcl)).

(* Halt does not step. We're going to distingush sucessful executions by looking at what
   was the last instruction *)

Lemma step_rules_instr : forall m i s pcv pcl s' e,
  step_rules (AState m i s (pcv,pcl)) e s' ->
  exists instr,
    index_list_Z pcv i = Some instr.
Proof.
  intros.
  inv H ; eauto.
Qed.

Lemma success_runSTO_None : forall  s,
  success s ->
  forall s' e, ~ step_rules s e s'.
Proof.
  intros. intros HCont. break_success.
  inv HCont; simpl in * ; try congruence.
Qed.

Lemma step_rules_non_ret_label_pc: forall m i stk pc l s instr e,
  step_rules (AState m i stk (pc, l)) e s ->
  index_list_Z pc i = Some instr ->
  instr <> Ret ->
  instr <> VRet ->
  exists (l' : T) (pc' : Z), apc s = (pc', l') /\ l <: l' = true.
Proof.
  intros.
  inv H; simpl in *; eauto.
  congruence.
  congruence.
Qed.

End ARuleMachine.
