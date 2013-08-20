Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Instr.
Require Import Concrete.
Require Import Semantics.
Require Import Memory.

Set Implicit Arguments.
Local Open Scope Z_scope.


Section CMach.

Notation "i @ pc # instr" := (index_list_Z pc i = Some instr) (no associativity, at level 55).
Notation "'__'" := dontCare.
Notation fh_start := (0,handlerTag).
Notation fh_ret := (fun pc pcl => (CRet (pc,pcl) false false)).

Notation Atom := (Atom Z privilege).
Notation memory := (Mem.t Atom privilege).
Notation PcAtom := (PcAtom Z).
Notation block := (block privilege).

Variable cblock : block.
Notation cache_hit_mem := (cache_hit_mem cblock).
Notation cache_hit_read_mem := (cache_hit_read_mem cblock).

Definition cget (m:memory) : option (list Atom) := Mem.get_frame m cblock.
Definition cupd (m:memory) (c:list Atom) : option memory := Mem.upd_frame m cblock c.

Definition c_alloc (p:privilege) (size:Z) (a:Atom) (m:memory) :=
  alloc Local p size a m.

(** Concrete machine transition relation.
    Each instructions has 3 semantic rules: (user mode - succ) (user mode - faulting) (kernel mode) *)

Inductive cstep : CS -> CEvent+τ -> CS -> Prop := 
| cstep_nop : forall m fh i s pcv pcl rl rpcl,
    forall (INST: i @ pcv # Noop)
           (CHIT: cache_hit_mem m (opCodeToZ OpNoop) (__,__,__) pcl)
           (CREAD: cache_hit_read_mem m rl rpcl),
    cstep (CState m fh i s (pcv,pcl) false)
          Silent (CState m fh i s (pcv+1,rpcl) false)

| cstep_nop_f : forall c' m fh i s pcv pcl m',
   forall (INST: i @ pcv # Noop)
          (CMISS: ~ cache_hit_mem m (opCodeToZ OpNoop) (__,__,__) pcl)
          (CUPD: c' = build_cache (opCodeToZ OpNoop) (__,__,__)  pcl)
          (CUPDGET: cupd m c' = Some m'),
    cstep (CState m fh i s (pcv,pcl) false) 
          Silent (CState m' fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_nop_p : forall m fh i s pcv pcl,
    fh @ pcv # Noop ->
    cstep (CState m fh i s (pcv,pcl) true) Silent (CState m fh i s (pcv+1,handlerTag) true)

| cstep_add: forall fh m i s rpcl pcv pcl rl x1v x1l x2v x2l v,
   forall(INST: i @ pcv # Add)
         (CHIT: cache_hit_mem m (opCodeToZ OpAdd) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl)
         (ADD: add x1v x2v = Some v),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           Silent (CState m fh i          ((v,rl):::s) (pcv+1,rpcl) false)

| cstep_add_f: forall c' fh m i s pcv pcl x1v x1l x2v x2l m',
   forall(INST: i @ pcv # Add)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpAdd) (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache (opCodeToZ OpAdd) (x1l,x2l,__)  pcl)
         (CUPDGET: cupd m c' = Some m'),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           Silent (CState m' fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_add_p: forall m fh i s pcv pcl x1v x1l x2v x2l v, 
    fh @ pcv # Add ->
    add x1v x2v = Some v ->
    cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)  
          Silent (CState m fh i ((v,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_sub: forall fh m i s rpcl pcv  pcl rl x1v x1l x2v x2l v,
   forall(INST: i @ pcv # Sub)
         (CHIT: cache_hit_mem m (opCodeToZ OpSub) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl)
         (SUB: sub x1v x2v = Some v),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           Silent (CState m fh i          ((v,rl):::s) (pcv+1,rpcl) false)

| cstep_sub_f: forall c' fh m i s pcv pcl x1v x1l x2v x2l m',
   forall(INST: i @ pcv # Sub)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpSub) (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache (opCodeToZ OpSub) (x1l,x2l,__)  pcl)
         (CUPDGET: cupd m c' = Some m'),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           Silent (CState m' fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_sub_p: forall m fh i s pcv pcl x1v x1l x2v x2l v, 
    fh @ pcv # Sub ->
    sub x1v x2v = Some v ->
    cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true) 
          Silent (CState m fh i ((v,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_eq: forall fh m i s rpcl pcv  pcl rl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Eq)
         (CHIT: cache_hit_mem m (opCodeToZ OpEq) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)
           Silent (CState m fh i          ((val_eq x1v x2v,rl):::s) (pcv+1,rpcl) false)

| cstep_eq_f: forall c' fh m i s pcv pcl x1v x1l x2v x2l m',
   forall(INST: i @ pcv # Eq)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpEq) (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache (opCodeToZ OpEq) (x1l,x2l,__)  pcl)
         (CUPDGET: cupd m c' = Some m'),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_eq_p: forall m fh i s pcv pcl x1v x1l x2v x2l,
    fh @ pcv # Eq ->
    cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)
          Silent (CState m fh i ((val_eq x1v x2v,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_dup_p: forall m fh i s pcv pcl n x,
    fh @ pcv # Dup n ->
    index_list n s = Some x ->
    cstep (CState m fh i s (pcv,pcl) true)
          Silent (CState m fh i (x::s) (pcv+1,handlerTag) true)

| cstep_swap_p: forall m fh i y s pcv pcl n x s',
    fh @pcv # Swap n -> 
    index_list n (y::s) = Some x ->
    update_list n y (x::s) = Some s' ->
    cstep (CState m fh i (y::s) (pcv,pcl) true)
          Silent (CState m fh i s' (pcv+1,handlerTag) true)

| cstep_push: forall fh m i s rpcl pcv pcl rl cv,
   forall(INST: i @ pcv # Push cv)
         (CHIT: cache_hit_mem m (opCodeToZ OpPush) (__ , __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i s (pcv,pcl)   false)
           Silent (CState m fh i ((Vint cv,rl):::s) (pcv+1,rpcl) false)

| cstep_push_f: forall c' fh m i s pcv pcl cv m',
   forall(INST : i @ pcv # Push cv)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpPush) (__,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpPush) (__,__,__) pcl)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i s (pcv,pcl) false)  
           Silent (CState m' fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_push_p: forall m fh i s pcv pcl cv, 
    fh @ pcv # Push cv ->
    cstep (CState m fh i s (pcv,pcl) true) 
          Silent (CState m fh i ((Vint cv,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_pop: forall fh m i s rpcl pcv pcl rl xv xl,
   forall(INST: i @ pcv # Pop)
         (CHIT: cache_hit_mem m (opCodeToZ OpPop) (__ , __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((xv,xl):::s) (pcv,pcl)   false)
           Silent (CState m fh i (s) (pcv+1,rpcl) false)

| cstep_pop_f: forall c' fh m i s pcv pcl xv xl m',
   forall(INST : i @ pcv # Pop)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpPop) (__,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpPop) (__,__,__) pcl)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i ((xv,xl):::s) (pcv,pcl) false)  
           Silent (CState m' fh i ((fh_ret pcv pcl)::(xv,xl):::s) fh_start true)

| cstep_pop_p: forall m fh i s pcv pcl xv xl, 
    fh @ pcv # Pop ->
    cstep (CState m fh i ((xv,xl):::s) (pcv,pcl) true) 
          Silent (CState m fh i s (pcv+1,handlerTag) true)

| cstep_push_cache_ptr_p: forall m fh i s pcv pcl, 
    fh @ pcv # PushCachePtr ->
    cstep (CState m fh i s (pcv,pcl) true) 
          Silent (CState m fh i ((Vptr cblock 0,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_alloc: forall fh m i s pcv pcl b size sizel xv xl m' rpcl rl,
               forall (INST: i @ pcv # Alloc)
                      (CHIT: cache_hit_mem m (opCodeToZ OpAlloc) (sizel, __, __) pcl)
                      (CREAD: cache_hit_read_mem m rl rpcl)
                      (ALLOC: c_alloc User size (xv,xl) m = Some (b,m')),
                 cstep (CState m fh i (CData (Vint size, sizel)::CData (xv,xl)::s) (pcv,pcl) false)
                       Silent
                       (CState m' fh i (CData (Vptr b 0,rl)::s) (pcv+1,rpcl) false)

| cstep_alloc_f: forall c' fh m m' i s pcv pcl size sizel xv xl,
                 forall (INST: i @ pcv # Alloc)
                        (CMISS: ~ cache_hit_mem m (opCodeToZ OpAlloc) (sizel, __, __) pcl)
                        (CUPD: c' = build_cache (opCodeToZ OpAlloc) (sizel, __, __) pcl)
                        (CUPDGET: cupd m c' = Some m'),
                   cstep (CState m fh i (CData (Vint size, sizel)::CData (xv,xl)::s) (pcv,pcl) false)
                         Silent
                         (CState m' fh i (fh_ret pcv pcl::CData (Vint size, sizel)::CData (xv,xl)::s) fh_start true)

| cstep_alloc_p: forall fh m m' i s pcv pcl b size sizel xv xl,
                 forall (INST: fh @ pcv # Alloc)
                        (ALLOC: c_alloc Kernel size (xv,xl) m = Some (b,m')),
                   cstep (CState m fh i (CData (Vint size, sizel)::CData (xv,xl)::s) (pcv,pcl) true)
                         Silent
                         (CState m' fh i (CData (Vptr b 0,handlerTag)::s) (pcv+1,handlerTag) true)

| cstep_load: forall fh m i s rpcl pcv pcl rl b ofs addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CHIT: cache_hit_mem m (opCodeToZ OpLoad) (addrl, xl, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl)
         (MREAD: load b ofs m = Some (xv,xl))
         (PRIV: Mem.stamp b = User),
     cstep (CState m fh i ((Vptr b ofs,addrl):::s) (pcv,pcl)   false)
           Silent (CState m fh i ((xv,rl):::s) (pcv+1,rpcl) false)

| cstep_load_f: forall c' fh m i s pcv pcl b ofs addrl xv xl m',
   forall(INST: i @ pcv # Load)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpLoad) (addrl,xl,__) pcl)
         (MREAD: load b ofs m = Some (xv,xl))
         (CUPD : c' = build_cache (opCodeToZ OpLoad) (addrl,xl,__) pcl)
         (PRIV: Mem.stamp b = User)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i ((Vptr b ofs,addrl):::s) (pcv,pcl)   false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::(Vptr b ofs,addrl):::s) fh_start true)

| cstep_load_p: forall m fh i s pcv pcl b ofs addrl xv xl,
   forall (INST: fh @ pcv # Load)
          (READ: load b ofs m = Some (xv,xl))
          (PRIV: Mem.stamp b = Kernel),
    cstep (CState m fh i ((Vptr b ofs,addrl):::s) (pcv,pcl) true) 
          Silent (CState m fh i ((xv,handlerTag):::s) (pcv+1,handlerTag) true)

| cstep_store: forall fh m m' i s rpcl pcv pcl rl b ofs addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CHIT: cache_hit_mem m (opCodeToZ OpStore) (addrl, xl, ml) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl)
         (MREAD: load b ofs m = Some (mv,ml))
         (MUPDT: store b ofs (xv,rl) m = Some m')
         (PRIV: Mem.stamp b = User),
     cstep (CState m fh i ((Vptr b ofs,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           Silent (CState m' fh i s (pcv+1,rpcl) false)

| cstep_store_f: forall c' fh m i s pcv pcl b ofs addrl xv xl mv ml m',
   forall(INST: i @ pcv # Store)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpStore) (addrl,xl,ml) pcl)
         (MREAD: load b ofs m = Some (mv,ml))
         (CUPD : c' = build_cache (opCodeToZ OpStore) (addrl,xl,ml) pcl)
         (PRIV: Mem.stamp b = User)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i ((Vptr b ofs,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::(Vptr b ofs,addrl):::(xv,xl):::s) fh_start true)

| cstep_store_p: forall m fh i s pcv pcl m' b ofs addrl x, 
    forall (INST:fh @ pcv # Store)
           (UPD: store b ofs x m = Some m')
           (PRIV: Mem.stamp b = Kernel),
    cstep (CState m fh i ((Vptr b ofs,addrl)::: x :::s) (pcv,pcl) true)
          Silent (CState m' fh i s (pcv+1,handlerTag) true)

| cstep_jump: forall fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Jump)
         (CHIT: cache_hit_mem m (opCodeToZ OpJump) (cl, __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((Vint cv,cl):::s) (pcv,pcl)   false)
           Silent (CState m fh i s (cv,rpcl) false)

| cstep_jump_f: forall c' fh m i s pcv pcl cv cl m',
   forall(INST: i @ pcv # Jump)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpJump) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpJump) (cl,__,__) pcl)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i ((cv,cl):::s) (pcv,pcl)   false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_jump_p: forall m fh i s pcv pcl pcj pcjl,
    forall (INST: fh @ pcv # Jump),
    cstep (CState m fh i ((Vint pcj,pcjl):::s) (pcv,pcl) true) 
          Silent (CState m fh i s (pcj,handlerTag) true)

| cstep_bnz: forall fh m i s rpcl pcv pcl rl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CHIT: cache_hit_mem m (opCodeToZ OpBranchNZ) (cl, __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((Vint cv,cl):::s) (pcv,pcl)   false)
           Silent (CState m fh i s (if cv =? 0 then pcv+1 else pcv+offv, rpcl) false)

| cstep_bnz_f: forall c' fh m m' i s pcv pcl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpBranchNZ) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpBranchNZ) (cl,__,__) pcl)
         (CUPDGET: cupd m c' = Some m'),
     cstep (CState m fh i ((Vint cv,cl):::s) (pcv,pcl)   false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::(Vint cv,cl):::s) fh_start true)

| cstep_branchnz_p: forall m fh i s pcv pcl offv av al,
    forall (INST: fh @ pcv # BranchNZ offv),
    cstep (CState m fh i ((Vint av,al):::s) (pcv,pcl) true) 
          Silent (CState m fh i s (if av =? 0 then pcv+1 else pcv+offv, handlerTag) true)

| cstep_call: forall fh m i s rpcl pcv pcl rl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGSA: length args = a) 
         (ARGS: forall a, In a args -> exists d, a = CData d)
         (CHIT: cache_hit_mem m (opCodeToZ OpCall) (pccl, __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((Vint pcc,pccl):::args++s) (pcv,pcl)   false)
           Silent (CState m fh i (args++(((CRet (pcv+1, rl)) r false)::s)) (pcc,rpcl) false)

| cstep_call_f: forall c' fh m i s pcv pcl pcc pccl a r args m',
   forall(INST: i @ pcv # Call a r)
         (ARGSA: length args = a) 
         (ARGS: forall a, In a args -> exists d, a = CData d)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpCall) (pccl, __, __) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpCall) (pccl,__,__) pcl)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i ((pcc,pccl):::args++s) (pcv,pcl)   false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::(pcc,pccl):::args++s) fh_start true)

| cstep_call_p: forall m fh i s pcv pcl a r args pcc pccl,
    forall (INST: fh @ pcv # Call a r)
           (ARGSA: length args = a)
           (ARGS: forall a, In a args -> exists d, a = CData d),
    cstep (CState m fh i ((Vint pcc,pccl):::args++s) (pcv,pcl) true) 
          Silent (CState m fh i (args++(CRet (pcv+1, pcl) r true)::s) (pcc, handlerTag) true)

| cstep_ret: forall fh m i s s' pcv pcl rl rpcl pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CHIT: cache_hit_mem m (opCodeToZ OpRet) (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false false)::s')) 
                (*DD: should only return to user mode *)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i s  (pcv,pcl) false)
           Silent (CState m fh i s' (pcret, rpcl) false)

| cstep_ret_f: forall c' fh m i s' s pcv pcl pret pcret pcretl m',
   forall(INST: i @ pcv # Ret)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpRet) (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s')) 
         (*DD: same thing, but we need not to constraint the return
               mode here, actually. *)
         (CUPD : c' = build_cache (opCodeToZ OpRet) (pcretl,__,__) pcl)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i s  (pcv,pcl) false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_ret_p: forall m fh i s pcv pcl  pcret pcretl s' pret, 
    forall (INST: fh @ pcv # Ret) (* can either return to user/priv mode *)
           (POP: c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s')),
    cstep (CState m fh i s  (pcv,pcl) true) 
          Silent (CState m fh i s' (pcret,pcretl) pret)

| cstep_vret: forall fh m i s s' pcv pcl rl rpcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CHIT: cache_hit_mem m (opCodeToZ OpVRet) (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) true false)::s')) 
                (*DD: should only return to user mode *)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((resv,resl):::s)  (pcv,pcl) false)
           Silent (CState m fh i ((resv,rl):::s') (pcret,rpcl) false)

| cstep_vret_f: forall c' fh m i s' s pcv pcl resv resl pcret pcretl m',
   forall(INST: i @ pcv # VRet)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpVRet) (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) true false)::s')) (*DD: same thing *)
         (CUPD : c' = build_cache (opCodeToZ OpVRet) (resl,pcretl,__) pcl)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i ((resv,resl):::s)  (pcv,pcl) false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::(resv,resl):::s) fh_start true)

| cstep_vret_p: forall m fh i s pcv pcl s' pcret pcretl resv resl, 
    forall (INST: fh @ pcv # VRet) (* cannot vreturn to user mode *)
           (POP: c_pop_to_return s ((CRet (pcret,pcretl) true true)::s')),
    cstep (CState m fh i ((resv,resl):::s) (pcv,pcl) true) 
          Silent (CState m fh i ((resv,resl):::s') (pcret, pcretl) true)

| cstep_out: forall fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Output)
         (CHIT: cache_hit_mem m (opCodeToZ OpOutput) (cl, __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((Vint cv,cl):::s) (pcv,pcl)   false)
           (E (CEInt (cv,rl))) (CState m fh i s (pcv+1,rpcl) false)

| cstep_out_f: forall c' fh m i s pcv pcl cv cl m',
   forall(INST: i @ pcv # Output)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpOutput) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpOutput) (cl,__,__) pcl)
         (CUPDGET : cupd m c' = Some m'),
     cstep (CState m fh i ((Vint cv,cl):::s) (pcv,pcl)   false)
           Silent (CState m' fh i ((fh_ret pcv pcl)::(Vint cv,cl):::s) fh_start true).

Definition initial_memory : memory :=
  (* Once again, it is OK to start with an empty cache. This will
  cause a miss on the first instruction, and after that the cache will
  grow to its true size *)
  Mem.init _ _ Local cblock nil.

Definition concrete_machine (faultHandler: list Instr) : semantics := 
  {| state := CS ;
    event := CEvent ;
    step := cstep ;
    init_data := list Instr * list PcAtom * Z;
    init_state := fun id => 
                    let '(p,d,def) := id in
                    {| mem := initial_memory;
                       fhdl := faultHandler;
                       imem := p;
                       stk := map (fun a:PcAtom => let (pc,l) := a in CData (Vint pc,l)) d;
                       pc := (0, def);
                       priv := false |}
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

