Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.

Require Import Instr.
Require Export Semantics.
Require Import AbstractCommon.

(** Definition of the step relation for the abstract machine. On each
step, the machine loads an instruction from the intruction memory at
the current program counter and executes it, producing a new state and
a possible output event. Errors such as stack underflows or invalid
memory accesses cause the machine to get stuck.  Each instruction uses
labels on atoms to track and control information flow. *)

Set Implicit Arguments.

Local Open Scope Z_scope.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Inductive a_step : @AS T -> (@Event T)+τ -> @AS T -> Prop :=
| step_nop : forall m i s pcv pcl
    (INSTR: index_list_Z pcv i = Some Noop),
    a_step (AState m i s (pcv,pcl)) τ (AState m i s (pcv+1,pcl))

| step_add: forall m i s pcv pcl x1v x1l x2v x2l
    (INSTR: index_list_Z pcv i = Some Add),
    a_step (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
           τ
           (AState m i ((AData (x1v+x2v,x1l \_/ x2l))::s) (pcv+1,pcl))
           
| step_sub: forall m i s pcv pcl x1v x1l x2v x2l
    (INSTR: index_list_Z pcv i = Some Sub),
    a_step (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
           τ
           (AState m i ((AData (x1v-x2v,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_push: forall m i s pcv pcl cv
    (INSTR: index_list_Z pcv i = Some (Push cv)),
    a_step (AState m i s (pcv,pcl))
           τ
           (AState m i ((AData (cv,bot))::s) (pcv+1,pcl))

| step_pop: forall m i s pcv pcl a
    (INSTR: index_list_Z pcv i = Some Pop),
    a_step (AState m i (AData a :: s) (pcv,pcl))
           τ
           (AState m i s (pcv+1,pcl))

| step_load: forall m i s pcv pcl addrv addrl xv xl
    (INSTR: index_list_Z pcv i = Some Load)
    (LOAD: index_list_Z addrv m = Some (xv,xl)),
    a_step (AState m i ((AData (addrv,addrl))::s) (pcv,pcl))
           τ
           (AState m i ((AData (xv,addrl \_/ xl)::s)) (pcv+1,pcl))

| step_store: forall m i s pcv pcl addrv addrl xv xl mv ml m'
    (INSTR: index_list_Z pcv i = Some Store)
    (LOAD: index_list_Z addrv m = Some (mv,ml))
    (CHECK: addrl \_/ pcl <: ml = true)
    (STORE: update_list_Z addrv (xv, addrl \_/ (xl \_/ pcl)) m = Some m'),
    a_step (AState m i ((AData (addrv,addrl))::(AData (xv,xl))::s) (pcv,pcl))
           τ
           (AState m' i s (pcv+1,pcl))

| step_jump: forall m i s pcv pcl pcv' pcl'
    (INSTR: index_list_Z pcv i = Some Jump),
    a_step (AState m i ((AData (pcv',pcl'))::s) (pcv,pcl))
           τ
           (AState m i s (pcv',pcl' \_/ pcl))

| step_branchnz_true: forall m i s pcv pcl offv al
    (INSTR: index_list_Z pcv i = Some (BranchNZ offv)), (* relative target *)
    a_step (AState m i ((AData (0,al))::s) (pcv,pcl))
           τ
           (AState m i s (pcv+1,al \_/ pcl))

| step_branchnz_false: forall m i s pcv pcl offv av al
    (INSTR: index_list_Z pcv i = Some (BranchNZ offv)) (* relative target *)
    (BRANCH: av <> 0),
    a_step (AState m i ((AData (av,al))::s) (pcv,pcl))
           τ
           (AState m i s (pcv+offv,al \_/ pcl))

| step_call: forall m i s pcv pcl pcv' pcl' args a r
    (INSTR: index_list_Z pcv i = Some (Call a r))
    (LENGTH: length args = a)
    (ARGS: forall a, In a args -> exists d, a = AData d),
    a_step (AState m i ((AData (pcv',pcl'))::args++s) (pcv,pcl))
           τ
           (AState m i (args++(ARet (pcv+1,pcl) r)::s) (pcv',pcl' \_/ pcl))

| step_ret: forall m i s pcv pcl pcv' pcl' s' 
    (INSTR: index_list_Z pcv i = Some Ret)
    (POP: pop_to_return s ((ARet (pcv',pcl') false)::s')),
    a_step (AState m i s (pcv,pcl)) τ (AState m i s' (pcv',pcl'))

| step_vret: forall m i s pcv pcl pcv' pcl' resv resl s' 
    (INSTR: index_list_Z pcv i = Some VRet)
    (POP: pop_to_return s ((ARet (pcv',pcl') true)::s')),
    a_step (AState m i (AData (resv,resl)::s) (pcv,pcl))
           τ 
           (AState m i (AData (resv, resl \_/ pcl)::s') (pcv',pcl'))

| step_output: forall m i s pcv pcl xv xl
    (INSTR: index_list_Z pcv i = Some Output),
    a_step (AState m i (AData (xv,xl)::s) (pcv,pcl))
           (E (EInt (xv,xl \_/ pcl))) (AState m i s (pcv+1,pcl)).

Lemma a_step_instr : forall m i s pcv pcl s' e,
  a_step (AState m i s (pcv,pcl)) e s' ->
  exists instr,
    index_list_Z pcv i = Some instr.
Proof.
  intros.
  inv H ; eauto.
Qed.

(** We pack everything related to the abstract machine in a [semantics]
record. 

In addition to the basic types and the step relation defined above, we
define a notion of initial data for the abstract machine, and a
function for constructing the initial machine state from this initial
data.

The initial data for the abstract machine is a tuple of the form
[(p,d,n,def)], where [p] is the program to load on the instruction
memory, [d] is a list of atoms to be pushed on the initial stack, [n]
is the size of the memory, and [def] is a default tag. Each memory
cell, as well as the pc, is initialized with a 0 labeled [def]. *)

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
