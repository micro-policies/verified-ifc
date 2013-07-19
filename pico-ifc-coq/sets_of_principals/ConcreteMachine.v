Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Instr.
Require Import Concrete.
Require Import Semantics.

Set Implicit Arguments.
Local Open Scope Z_scope.


Section CMach.

Notation "i @ pc # instr" := (index_list_Z pc i = Some instr) (no associativity, at level 55).
Notation "'__'" := dontCare.
Notation fh_start := (0,handlerTag).
Notation fh_ret := (fun pc pcl => (CRet (pc,pcl) false false)).
Notation fh_vret := (fun pc pcl => (CRet (pc,pcl) true false)).

(** Concrete machine transition relation.
    Each instructions has 3 semantic rules: (user mode - succ) (user mode - faulting) (kernel mode) *)
Context {T:Type}.
Variable SysTable : syscall_table T.

Inductive cstep : CS -> CEvent+τ -> CS -> Prop :=
| cstep_nop : forall c m fh i s pcv pcl rl rpcl,
    forall (INST: i @ pcv # Noop)
           (CHIT: cache_hit c (opCodeToZ OpNoop) (__,__,__) pcl)
           (CREAD: cache_hit_read c rl rpcl),
    cstep (CState c m fh i s (pcv,pcl) false)
          Silent (CState c m fh i s (pcv+1,rpcl) false)

| cstep_nop_f : forall c c' m fh i s pcv pcl,
   forall (INST: i @ pcv # Noop)
          (CMISS: ~ cache_hit c (opCodeToZ OpNoop) (__,__,__) pcl)
          (CUPD: c' = update_cache (opCodeToZ OpNoop) (__,__,__)  pcl c),
    cstep (CState c m fh i s (pcv,pcl) false)
          Silent (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_nop_p : forall c m fh i s pcv pcl,
    fh @ pcv # Noop ->
    cstep (CState c m fh i s (pcv,pcl) true) Silent (CState c m fh i s (pcv+1,handlerTag) true)

| cstep_add: forall c fh m i s rpcl pcv pcl rl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Add)
         (CHIT: cache_hit c (opCodeToZ OpAdd) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)
           Silent (CState c m fh i          ((x1v+x2v,rl):::s) (pcv+1,rpcl) false)

| cstep_add_f: forall c c' fh m i s pcv pcl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Add)
         (CMISS: ~ cache_hit c (opCodeToZ OpAdd) (x1l, x2l, __) pcl)
         (CUPD: c' = update_cache (opCodeToZ OpAdd) (x1l,x2l,__)  pcl c),
     cstep (CState c  m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_add_p: forall c m fh i s pcv pcl x1v x1l x2v x2l,
    fh @ pcv # Add ->
    cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)
          Silent (CState c m fh i ((x1v+x2v,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_sub: forall c fh m i s rpcl pcv  pcl rl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Sub)
         (CHIT: cache_hit c (opCodeToZ OpSub) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)
           Silent (CState c m fh i          ((x1v-x2v,rl):::s) (pcv+1,rpcl) false)

| cstep_sub_f: forall c c' fh m i s pcv pcl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Sub)
         (CMISS: ~ cache_hit c (opCodeToZ OpSub) (x1l, x2l, __) pcl)
         (CUPD: c' = update_cache (opCodeToZ OpSub) (x1l,x2l,__)  pcl c),
     cstep (CState c  m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_sub_p: forall c m fh i s pcv pcl x1v x1l x2v x2l,
    fh @ pcv # Sub ->
    cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)
          Silent (CState c m fh i ((x1v-x2v,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_dup_p: forall c m fh i s pcv pcl n x,
    fh @ pcv # Dup n ->
    index_list n s = Some x ->
    cstep (CState c m fh i s (pcv,pcl) true)
          Silent (CState c m fh i (x::s) (pcv+1,pcl) true)

| cstep_swap_p: forall c m fh i y s pcv pcl n x s',
    fh @pcv # Swap n ->
    index_list n (y::s) = Some x ->
    update_list n y (x::s) = Some s' ->
    cstep (CState c m fh i (y::s) (pcv,pcl) true)
          Silent (CState c m fh i s' (pcv+1,pcl) true)

| cstep_push: forall c fh m i s rpcl pcv pcl rl cv,
   forall(INST: i @ pcv # Push cv)
         (CHIT: cache_hit c (opCodeToZ OpPush) (__ , __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i s (pcv,pcl)   false)
           Silent (CState c m fh i ((cv,rl):::s) (pcv+1,rpcl) false)

| cstep_push_f: forall c c' fh m i s pcv pcl cv,
   forall(INST : i @ pcv # Push cv)
         (CMISS: ~ cache_hit c (opCodeToZ OpPush) (__,__,__) pcl)
         (CUPD : c' = update_cache (opCodeToZ OpPush) (__,__,__) pcl c),
     cstep (CState c  m fh i s (pcv,pcl) false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_push_p: forall c m fh i s pcv pcl cv,
    fh @ pcv # Push cv ->
    cstep (CState c m fh i s (pcv,pcl) true)
          Silent (CState c m fh i ((cv,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_pop: forall c fh m i s rpcl pcv pcl a rl,
   forall(INST: i @ pcv # Pop)
         (CHIT: cache_hit c (opCodeToZ OpPop) (__,__,__) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i (a ::: s) (pcv,pcl) false)
           Silent (CState c m fh i s (pcv+1,rpcl) false)

| cstep_pop_f: forall c c' fh m i s pcv pcl a,
   forall(INST: i @ pcv # Pop)
         (CMISS: ~ cache_hit c (opCodeToZ OpPop) (__,__,__) pcl)
         (CUPD: c' = update_cache (opCodeToZ OpPop) (__,__,__) pcl c),
     cstep (CState c m fh i (a ::: s) (pcv,pcl) false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::a:::s) fh_start true)

| cstep_pop_p: forall c fh m i s pcv pcl a,
    fh @ pcv # Pop ->
    cstep (CState c m fh i (a ::: s) (pcv,pcl) true)
          Silent (CState c m fh i s (pcv+1,handlerTag) true)

| cstep_load: forall c fh m i s rpcl pcv pcl rl addrv addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CHIT: cache_hit c (opCodeToZ OpLoad) (addrl, xl, __) pcl)
         (CREAD: cache_hit_read c rl rpcl)
         (MREAD: read_m addrv m = Some (xv,xl)),
     cstep (CState c m fh i ((addrv,addrl):::s) (pcv,pcl)   false)
           Silent (CState c m fh i ((xv,rl):::s) (pcv+1,rpcl) false)

| cstep_load_f: forall c c' fh m i s pcv pcl addrv addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CMISS: ~ cache_hit c (opCodeToZ OpLoad) (addrl,xl,__) pcl)
         (MREAD: read_m addrv m = Some (xv,xl))
         (CUPD : c' = update_cache (opCodeToZ OpLoad) (addrl,xl,__) pcl c),
     cstep (CState c  m fh i ((addrv,addrl):::s) (pcv,pcl)   false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(addrv,addrl):::s) fh_start true)

| cstep_load_p: forall c m fh i s pcv pcl addrv addrl xv xl,
    fh @ pcv # Load ->
    read_m addrv c = Some (xv,xl) ->
    cstep (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) true)
          Silent (CState c m fh i ((xv,xl):::s) (pcv+1,handlerTag) true)

| cstep_store: forall c fh m m' i s rpcl pcv pcl rl addrv addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CHIT: cache_hit c (opCodeToZ OpStore) (addrl, xl, ml) pcl)
         (CREAD: cache_hit_read c rl rpcl)
         (MREAD: read_m addrv m = Some (mv,ml))
         (MUPDT: upd_m addrv (xv,rl) m = Some m'),
     cstep (CState c m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           Silent (CState c m' fh i s (pcv+1,rpcl) false)

| cstep_store_f: forall c c' fh m i s pcv pcl addrv addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CMISS: ~ cache_hit c (opCodeToZ OpStore) (addrl,xl,ml) pcl)
         (MREAD: read_m addrv m = Some (mv,ml))
         (CUPD : c' = update_cache (opCodeToZ OpStore) (addrl,xl,ml) pcl c),
     cstep (CState c  m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(addrv,addrl):::(xv,xl):::s) fh_start true)

| cstep_store_p: forall c m fh i s pcv pcl c' addrv addrl xv xl,
    fh @ pcv # Store ->
    upd_m addrv (xv,xl) c = Some c' ->
    cstep (CState c m fh i ((addrv,addrl)::: (xv,xl) :::s) (pcv,pcl) true)
          Silent (CState c' m fh i s (pcv+1,handlerTag) true)

| cstep_jump: forall c fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Jump)
         (CHIT: cache_hit c (opCodeToZ OpJump) (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((cv,cl):::s) (pcv,pcl)   false)
           Silent (CState c m fh i s (cv,rpcl) false)

| cstep_jump_f: forall c c' fh m i s pcv pcl cv cl,
   forall(INST: i @ pcv # Jump)
         (CMISS: ~ cache_hit c (opCodeToZ OpJump) (cl,__,__) pcl)
         (CUPD : c' = update_cache (opCodeToZ OpJump) (cl,__,__) pcl c),
     cstep (CState c  m fh i ((cv,cl):::s) (pcv,pcl)   false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_jump_p: forall c m fh i s pcv pcl pcj pcjl,
    fh @ pcv # Jump ->
    cstep (CState c m fh i ((pcj,pcjl):::s) (pcv,pcl) true)
          Silent (CState c m fh i s (pcj,handlerTag) true)

| cstep_bnz: forall c fh m i s rpcl pcv pcl rl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CHIT: cache_hit c (opCodeToZ OpBranchNZ) (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((cv,cl):::s) (pcv,pcl)   false)
           Silent (CState c m fh i s (if cv =? 0 then pcv+1 else pcv+offv, rpcl) false)

| cstep_bnz_f: forall c c' fh m i s pcv pcl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CMISS: ~ cache_hit c (opCodeToZ OpBranchNZ) (cl,__,__) pcl)
         (CUPD : c' = update_cache (opCodeToZ OpBranchNZ) (cl,__,__) pcl c),
     cstep (CState c  m fh i ((cv,cl):::s) (pcv,pcl)   false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_branchnz_p: forall c m fh i s pcv pcl offv av al,
    fh @ pcv # BranchNZ offv ->
    cstep (CState c m fh i ((av,al):::s) (pcv,pcl) true)
          Silent (CState c m fh i s (if av =? 0 then pcv+1 else pcv+offv, handlerTag) true)

| cstep_call: forall c fh m i s rpcl pcv pcl rl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGSA: length args = a)
         (ARGS: forall a, In a args -> exists d, a = CData d)
         (CHIT: cache_hit c (opCodeToZ OpCall) (pccl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl)   false)
           Silent (CState c m fh i (args++(((CRet (pcv+1, rl)) r false)::s)) (pcc,rpcl) false)

| cstep_call_f: forall c c' fh m i s pcv pcl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGSA: length args = a)
         (ARGS: forall a, In a args -> exists d, a = CData d)
         (CMISS: ~ cache_hit c (opCodeToZ OpCall) (pccl, __, __) pcl)
         (CUPD : c' = update_cache (opCodeToZ OpCall) (pccl,__,__) pcl c),
     cstep (CState c  m fh i ((pcc,pccl):::args++s) (pcv,pcl)   false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(pcc,pccl):::args++s) fh_start true)

| cstep_call_p: forall c m fh i s pcl pcv a r args pcc pccl,
    fh @ pcv # Call a r ->
    length args = a -> (forall a, In a args -> exists d, a = CData d) ->
    cstep (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl) true)
          Silent (CState c m fh i (args++(CRet (pcv+1, handlerTag) r true)::s) (pcc, handlerTag) true)

| cstep_ret: forall c fh m i s s' pcv pcl rl rpcl pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CHIT: cache_hit c (opCodeToZ OpRet) (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false false)::s'))
                (*DD: should only return to user mode *)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i s  (pcv,pcl) false)
           Silent (CState c m fh i s' (pcret, rpcl) false)

| cstep_ret_f: forall c c' fh m i s' s pcv pcl pret pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CMISS: ~ cache_hit c (opCodeToZ OpRet) (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s'))
         (*DD: same thing, but we need not to constraint the return
               mode here, actually. *)
         (CUPD : c' = update_cache (opCodeToZ OpRet) (pcretl,__,__) pcl c),
     cstep (CState c m fh i s  (pcv,pcl) false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_ret_p: forall c m fh i s pcv pcl pcret pcretl s' pret,
    fh @ pcv # Ret -> (* can either return to user/priv mode *)
    c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s') ->
    cstep (CState c m fh i s  (pcv,pcl) true)
          Silent (CState c m fh i s' (pcret,pcretl) pret)

| cstep_vret: forall c fh m i s s' pcv pcl rl rpcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CHIT: cache_hit c (opCodeToZ OpVRet) (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) true false)::s'))
                (*DD: should only return to user mode *)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((resv,resl):::s)  (pcv,pcl) false)
           Silent (CState c m fh i ((resv,rl):::s') (pcret,rpcl) false)

| cstep_vret_f: forall c c' fh m i s' s pcv pcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CMISS: ~ cache_hit c (opCodeToZ OpVRet) (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) true false)::s')) (*DD: same thing *)
         (CUPD : c' = update_cache (opCodeToZ OpVRet) (resl,pcretl,__) pcl c),
     cstep (CState c m fh i ((resv,resl):::s)  (pcv,pcl) false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(resv,resl):::s) fh_start true)

| cstep_vret_p: forall c m fh i s pcv pcl s' pcret pcretl resv resl pret,
    fh @ pcv # VRet -> (* APT: changed to allow vret to user mode, used for system calls *)
    c_pop_to_return s ((CRet (pcret,pcretl) true pret)::s') ->
    cstep (CState c m fh i ((resv,resl):::s) (pcv,pcl) true)
          Silent (CState c m fh i ((resv,resl):::s') (pcret, pcretl) pret)

| cstep_out: forall c fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Output)
         (CHIT: cache_hit c (opCodeToZ OpOutput) (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((cv,cl):::s) (pcv,pcl)   false)
           (E (CEInt (cv,rl) c)) (CState c m fh i s (pcv+1,rpcl) false)

| cstep_out_f: forall c c' fh m i s pcv pcl cv cl,
   forall(INST: i @ pcv # Output)
         (CMISS: ~ cache_hit c (opCodeToZ OpOutput) (cl,__,__) pcl)
         (CUPD : c' = update_cache (opCodeToZ OpOutput) (cl,__,__) pcl c),
     cstep (CState c  m fh i ((cv,cl):::s) (pcv,pcl)   false)
           Silent (CState c' m fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_alloc_p: forall c c' fh m i s pcv pcl xv xl a,
    fh @ pcv # Alloc ->
    (a,c') = malloc xv (0,handlerTag) c -> (* specify initializing value to keep machine deterministic *)
    cstep (CState c m fh i ((xv,xl):::s) (pcv,pcl) true)
          Silent (CState c' m fh i ((a,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_unpack_p :forall c fh m i xv xl s pcv pcl,
    fh @ pcv # Unpack ->
    cstep (CState c m fh i ((xv,xl):::s) (pcv,pcl) true)  (* unpacked payload carries handlerTag *)
          Silent (CState c m fh i ((xl,handlerTag):::(xv,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_pack_p :forall c fh m i xv xvl xl xll s pcv pcl,
    fh @ pcv # Pack ->
    cstep (CState c m fh i ((xl,xll):::(xv,xvl):::s) (pcv,pcl) true)
          Silent (CState c m fh i ((xv,xl):::s) (pcv+1,handlerTag) true)

| cstep_syscall: forall id c fh m i s pcv pcl sys_info args,
   forall(INST: i @ pcv # (SysCall id))
         (SYS: SysTable id = Some sys_info)
         (SYSLENGTH: length args = sys_info.(si_arity)),
     cstep (CState c m fh i (args ++ s) (pcv,pcl) false)
           Silent
           (CState c m fh i (args ++ (fh_vret (pcv+1) pcl) :: s) (sys_info.(si_pc),handlerTag) true)
.

(* Invalid starting cache *)
Definition initial_cache : list (@Atom Z) :=
  build_cache invalidOpCode (0,0,0) 0.

Definition concrete_machine
           (kernel: list Instr)
           (init_data: Type)
           (init_state : init_data -> (list Instr *     (* program *)
                                       list (@Atom Z) * (* kernel mem, not including cache *)
                                       list (@Atom Z) * (* user mem *)
                                       list CStkElmt *  (* stack *)
                                       Z                (* default tag *)
           )) : semantics :=
  {| state := CS ;
     event := CEvent ;
     step := cstep ;
     init_data := init_data;
     init_state := fun id => let '(p,km,m,s,def) := (init_state id) in
                             (CState (initial_cache++km) 
                                     m 
                                     kernel
                                     p s (0,def) false)
  |}.

Lemma priv_no_event_l : forall s e s'
                               (STEP : cstep s e s')
                               (PRIV : priv s = true),
                          e = Silent.
Proof.
  intros.
  inv STEP; simpl in *; try congruence; auto.
Qed.

Lemma priv_no_event_r : forall s e s'
                               (STEP : cstep s e s')
                               (PRIV : priv s' = true),
                          e = Silent.
Proof.
  intros.
  inv STEP; simpl in *; try congruence; auto.
Qed.

End CMach.
