Require Import List.
Require Import Omega.
Require Import EquivDec.


Require Import Utils.
Require Import Lattices.

Require Import Instr Memory.
Require Export Semantics.
Require Import AbstractCommon.

Set Implicit Arguments.

Local Open Scope Z_scope.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {EqT: EqDec T eq}.

Variable table : ASysTable T.

Definition a_state := AS T T. (* We stamp block with allocation label *)
Definition a_alloc 
      (size:Z) (lpc:T) (a:Atom T T) (m:memory T T): option (block T * memory T T) :=
  alloc Local lpc size a m.

Inductive a_step : a_state -> (Event T)+τ -> a_state -> Prop :=
| step_nop : forall m i s pcv pcl
    (INSTR: index_list_Z pcv i = Some Noop),
    a_step (AState m i s (pcv,pcl)) Silent (AState m i s (pcv+1,pcl))

| step_add: forall m i s pcv pcl x1v x1l x2v x2l xv
    (INSTR: index_list_Z pcv i = Some Add)
    (ADD: add x1v x2v = Some xv),
    a_step (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               Silent
               (AState m i ((AData (xv,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_sub: forall m i s pcv pcl x1v x1l x2v x2l xv
    (INSTR: index_list_Z pcv i = Some Sub)
    (SUB: sub x1v x2v = Some xv),
    a_step (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               Silent
               (AState m i ((AData (xv,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_eq: forall m i s pcv pcl x1v x1l x2v x2l
    (INSTR: index_list_Z pcv i = Some Eq),
    a_step (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               Silent
               (AState m i ((AData (val_eq x1v x2v,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_dup : forall m i s1 s2 pcv pcl n x
    (INSTR: index_list_Z pcv i = Some (Dup n))
    (IDX: index_list n s1 = Some x)
    (DATA: forall se, In se s1 -> exists a, se = AData a),
    a_step (AState m i (s1 ++ s2) (pcv, pcl))
           Silent
           (AState m i (x :: s1 ++ s2) (pcv+1,pcl))

| step_swap : forall m i s1 s1' s2 pcv pcl n
    (INSTR: index_list_Z pcv i = Some (Swap n))
    (SWAP: swap n s1 = Some s1')
    (DATA: forall se, In se s1 -> exists a, se = AData a),
    a_step (AState m i (s1 ++ s2) (pcv, pcl))
           Silent
           (AState m i (s1' ++ s2) (pcv+1,pcl))

| step_push: forall m i s pcv pcl cv
    (INSTR: index_list_Z pcv i = Some (Push cv)),
    a_step (AState m i s (pcv,pcl))
               Silent
               (AState m i ((AData (Vint cv,bot))::s) (pcv+1,pcl))

| step_pop: forall m i s pcv pcl a
    (INSTR: index_list_Z pcv i = Some Pop),
    a_step (AState m i (AData a :: s) (pcv,pcl))
               Silent
               (AState m i s (pcv+1,pcl))

| step_alloc: forall m i s pcv pcl b size sizel xv xl m'
    (INSTR: index_list_Z pcv i = Some Alloc)
    (ALLOC: a_alloc size (sizel \_/ pcl) (xv,xl) m = Some (b,m')),
    a_step (AState m i ((AData (Vint size,sizel))::(AData (xv,xl))::s) (pcv,pcl))
               Silent
               (AState m' i (AData (Vptr b 0,sizel \_/ pcl)::s) (pcv+1,pcl))

| step_load: forall m i s pcv pcl addrl b ofs xv xl
    (INSTR: index_list_Z pcv i = Some Load)
    (LOAD: load b ofs m = Some (xv,xl)),
    a_step (AState m i ((AData (Vptr b ofs,addrl))::s) (pcv,pcl))
               Silent
               (AState m i ((AData (xv,addrl \_/ xl)::s)) (pcv+1,pcl))

| step_store: forall m i s pcv pcl b ofs addrl xv xl mv ml m'
    (INSTR: index_list_Z pcv i = Some Store)
    (LOAD: load b ofs m = Some (mv,ml))
    (CHECK: addrl \_/ pcl <: ml = true)
    (STORE: store b ofs (xv, addrl \_/ (xl \_/ pcl)) m = Some m'),
    a_step (AState m i ((AData (Vptr b ofs,addrl))::(AData (xv,xl))::s) (pcv,pcl))
               Silent
               (AState m' i s (pcv+1,pcl))

| step_jump: forall m i s pcv pcl pcv' pcl'
    (INSTR: index_list_Z pcv i = Some Jump),
    a_step (AState m i ((AData (Vint pcv',pcl'))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv',pcl' \_/ pcl))

| step_branchnz_true: forall m i s pcv pcl offv al
    (INSTR: index_list_Z pcv i = Some (BranchNZ offv)), (* relative target *)
    a_step (AState m i ((AData (Vint 0,al))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv+1,al \_/ pcl))

| step_branchnz_false: forall m i s pcv pcl offv av al
    (INSTR: index_list_Z pcv i = Some (BranchNZ offv)) (* relative target *)
    (BRANCH: av <> 0),
    a_step (AState m i ((AData (Vint av,al))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv+offv,al \_/ pcl))

| step_call: forall m i s pcv pcl pcv' pcl' args a r
    (INSTR: index_list_Z pcv i = Some (Call a r))
    (LENGTH: length args = a)
    (ARGS: forall a, In a args -> exists d, a = AData d),
    a_step (AState m i ((AData (Vint pcv',pcl'))::args++s) (pcv,pcl))
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
    a_step (AState m i (AData (Vint xv,xl)::s) (pcv,pcl))
               (E (EInt (xv,xl \_/ pcl))) (AState m i s (pcv+1,pcl))


| step_syscall: forall id m i s pcv pcl args res sys_info
    (INSTR: index_list_Z pcv i = Some (SysCall id))
    (SYS: table id = Some sys_info)
    (SYSLENGTH: length args = sys_info.(asi_arity))
    (SYSSEM: sys_info.(asi_sem) args = Some res), (* this encodes potential IFC check failures *)
    a_step (AState m i (map AData args ++ s) (pcv,pcl))
           Silent (AState m i (AData res :: s) (pcv+1,pcl))

| step_sizeof: forall m i s pcv pcl b off pl fr
    (INSTR: index_list_Z pcv i = Some SizeOf)
    (FRAME: Mem.get_frame m b = Some fr),
    a_step (AState m i (AData (Vptr b off, pl)::s) (pcv,pcl))
           Silent (AState m i (AData (Vint (Z.of_nat (length fr)), pl)::s) (pcv+1,pcl)).

Lemma a_step_instr : forall m i s pcv pcl s' e,
  a_step (AState m i s (pcv,pcl)) e s' ->
  exists instr,
    index_list_Z pcv i = Some instr.
Proof.
  intros m i s pcv pcl s' e H.
  inv H ; eauto.
Qed.

Definition abstract_machine := 
  {| state := a_state ;
    event := (Event T) ;
    step := a_step ;
    init_data := abstract_init_data T;
    init_state := fun id =>
                    let '(p,d,b) := id in
                    {| amem := Mem.empty _ _;
                       aimem := p ;
                       astk := map (fun a: (Z*T) => let (i,l) := a in AData (Vint i,l)) d;
                       apc := (0%Z, b) |}
  |}.
                  
End ARuleMachine.
