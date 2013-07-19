Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.

Require Import Instr.
Require Export Semantics.
Require Import AbstractCommon.

Set Implicit Arguments.

Local Open Scope Z_scope.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.
Variable SysTable: syscall_table T.

Inductive a_step : @AS T -> (@Event T)+τ -> @AS T -> Prop :=
| step_nop : forall m i s pcv pcl
    (INSTR: index_list_Z pcv i = Some Noop),
    a_step (AState m i s (pcv,pcl)) Silent (AState m i s (pcv+1,pcl))

| step_add: forall m i s pcv pcl x1v x1l x2v x2l
    (INSTR: index_list_Z pcv i = Some Add),
    a_step (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               Silent
               (AState m i ((AData (x1v+x2v,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_sub: forall m i s pcv pcl x1v x1l x2v x2l
    (INSTR: index_list_Z pcv i = Some Sub),
    a_step (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               Silent
               (AState m i ((AData (x1v-x2v,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_push: forall m i s pcv pcl cv
    (INSTR: index_list_Z pcv i = Some (Push cv)),
    a_step (AState m i s (pcv,pcl))
               Silent
               (AState m i ((AData (cv,bot))::s) (pcv+1,pcl))

| step_pop: forall m i s pcv pcl a
    (INSTR: index_list_Z pcv i = Some Pop),
    a_step (AState m i (AData a :: s) (pcv,pcl))
               Silent
               (AState m i s (pcv+1,pcl))

| step_load: forall m i s pcv pcl addrv addrl xv xl
    (INSTR: index_list_Z pcv i = Some Load)
    (LOAD: index_list_Z addrv m = Some (xv,xl)),
    a_step (AState m i ((AData (addrv,addrl))::s) (pcv,pcl))
               Silent
               (AState m i ((AData (xv,addrl \_/ xl)::s)) (pcv+1,pcl))

| step_store: forall m i s pcv pcl addrv addrl xv xl mv ml m'
    (INSTR: index_list_Z pcv i = Some Store)
    (LOAD: index_list_Z addrv m = Some (mv,ml))
    (CHECK: addrl \_/ pcl <: ml = true)
    (STORE: update_list_Z addrv (xv, addrl \_/ (xl \_/ pcl)) m = Some m'),
    a_step (AState m i ((AData (addrv,addrl))::(AData (xv,xl))::s) (pcv,pcl))
               Silent
               (AState m' i s (pcv+1,pcl))

| step_jump: forall m i s pcv pcl pcv' pcl'
    (INSTR: index_list_Z pcv i = Some Jump),
    a_step (AState m i ((AData (pcv',pcl'))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv',pcl' \_/ pcl))

| step_branchnz_true: forall m i s pcv pcl offv al
    (INSTR: index_list_Z pcv i = Some (BranchNZ offv)), (* relative target *)
    a_step (AState m i ((AData (0,al))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv+1,al \_/ pcl))

| step_branchnz_false: forall m i s pcv pcl offv av al
    (INSTR: index_list_Z pcv i = Some (BranchNZ offv)) (* relative target *)
    (BRANCH: av <> 0),
    a_step (AState m i ((AData (av,al))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv+offv,al \_/ pcl))

| step_call: forall m i s pcv pcl pcv' pcl' args a r
    (INSTR: index_list_Z pcv i = Some (Call a r))
    (LENGTH: length args = a)
    (ARGS: forall a, In a args -> exists d, a = AData d),
    a_step (AState m i ((AData (pcv',pcl'))::args++s) (pcv,pcl))
               Silent
               (AState m i (args++(ARet (pcv+1,pcl) r)::s) (pcv',pcl' \_/ pcl))

| step_ret: forall m i s pcv pcl pcv' pcl' s' 
    (INSTR: index_list_Z pcv i = Some Ret)
    (POP: pop_to_return s ((ARet (pcv',pcl') false)::s')),
    a_step (AState m i s (pcv,pcl)) Silent (AState m i s' (pcv',pcl'))

| step_vret: forall m i s pcv pcl pcv' pcl' resv resl s' 
    (INSTR: index_list_Z pcv i = Some VRet)
    (POP: pop_to_return s ((ARet (pcv',pcl') true)::s')),
    a_step (AState m i (AData (resv,resl)::s) (pcv,pcl))
               Silent (AState m i (AData (resv, resl \_/ pcl)::s') (pcv',pcl'))

| step_output: forall m i s pcv pcl xv xl
    (INSTR: index_list_Z pcv i = Some Output),
    a_step (AState m i (AData (xv,xl)::s) (pcv,pcl))
               (E (EInt (xv,xl \_/ pcl))) (AState m i s (pcv+1,pcl))

| step_syscall: forall id m i s pcv pcl args res sys_info
    (INSTR: index_list_Z pcv i = Some (SysCall id))
    (SYS: SysTable id = Some sys_info)
    (SYSLENGTH: length args = sys_info.(si_arity))
    (SYSSEM: sys_info.(si_sem) args = Some res), (* this encodes potential IFC check failures *)
    a_step (AState m i (map AData args ++ s) (pcv,pcl)) 
           Silent (AState m i (AData res :: s) (pcv+1,pcl)).

Lemma a_step_instr : forall m i s pcv pcl s' e,
  a_step (AState m i s (pcv,pcl)) e s' ->
  exists instr,
    index_list_Z pcv i = Some instr.
Proof.
  intros.
  inv H ; eauto.
Qed.

Definition abstract_machine : semantics := 
  {| state := AS ;
    event := Event ;
    step := a_step ;
    init_data := list Instr * list (@Atom T) * nat * T ;
    init_state := fun id => 
                    let '(p,d,n,def) := id in
                    {| amem := replicate (0%Z, def) n ;
                       aimem := p ;
                       astk := map (fun a => AData a) d;
                       apc := (0%Z, def) |}
  |}.
                  
End ARuleMachine.
