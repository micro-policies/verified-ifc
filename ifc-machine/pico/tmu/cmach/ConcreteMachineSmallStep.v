Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import CLattices.
Require Import Concrete.

Set Implicit Arguments.
Local Open Scope Z_scope.

(** Reflexive transitive closure. *)
(* to be moved in Utils *)

Definition op_cons (E: Type) (oe: option E) (l: list E) :=
  match oe with 
      | Some e => e::l
      | None => l
  end.

Inductive star (S E: Type) (Rstep: S -> option E -> S -> Prop): S -> list E -> S -> Prop :=
  | star_refl: forall s,
      star Rstep s nil s
  | star_step: forall s1 s2 s3 e t t',
      Rstep s1 e s2 -> star Rstep s2 t s3 -> 
      t' = (op_cons e t) ->
      star Rstep s1 t' s3.
Hint Constructors star.

Lemma op_cons_app : forall E (e: option E) t t', (op_cons e t)++t' = op_cons e (t++t').
Proof. intros. destruct e; reflexivity. Qed.  

Lemma star_right : forall S E (Rstep: S -> option E -> S -> Prop) s1 s2 t, 
                     star Rstep s1 t s2 -> 
                     forall s3 e t', 
                       Rstep s2 e s3 -> 
                       t' = (t++(op_cons e nil)) ->
                       star Rstep s1 t' s3.
Proof.
  induction 1; intros.
  eapply star_step; eauto.
  exploit IHstar; eauto. intros.
  inv H3. rewrite op_cons_app; eauto. 
Qed.

Inductive plus (S E: Type) (Rstep: S -> option E -> S -> Prop): S -> list E -> S -> Prop :=
  | plus_step: forall s t s' e,
      Rstep s e s' ->
      t = (op_cons e nil) ->
      plus Rstep s t s'
  | plus_trans: forall s1 s2 s3 e t t',
      Rstep s1 e s2 -> plus Rstep s2 t s3 -> 
      t' = (op_cons e t) ->
      plus Rstep s1 t' s3.

Hint Constructors star.
Hint Constructors plus.

Lemma plus_right : forall E S (Rstep: S -> option E -> S -> Prop) s1 s2 t, 
                     plus Rstep s1 t s2 -> 
                     forall s3 e t',
                       t' = (t++(op_cons e nil)) ->
                       Rstep s2 e s3 -> plus Rstep s1 t' s3.
Proof.
  induction 1; intros.
  inv H1.
  rewrite op_cons_app. simpl.
  eapply plus_trans; eauto.
  exploit IHplus; eauto.
  inv H2. rewrite op_cons_app.  eauto.
Qed.

Section CMach.

Notation "i @ pc # instr" := (index_list_Z pc i = Some instr) (no associativity, at level 55).
Notation "'__'" := dontCare.
Notation fh_start := (0,handlerTag).
Notation fh_ret := (fun pc pcl => (CRet (pc,pcl) false false)).

(** Concrete machine transition relation.
    Each instructions has 3 semantic rules: (user mode - succ) (user mode - faulting) (kernel mode) *)

Inductive cstep : CS -> option CEvent -> CS -> Prop := 
| cstep_nop : forall c m fh i s pcv pcl rl rpcl,
    forall (INST: i @ pcv # Noop)
           (CHIT: cache_hit c (opCodeToZ OpNoop) (__,__,__) pcl)
           (CREAD: cache_hit_read c rl rpcl),
    cstep (CState c m fh i s (pcv,pcl) false)
          None (CState c m fh i s (pcv+1,rpcl) false)

| cstep_nop_f : forall c c' m fh i s pcv pcl,
   forall (INST: i @ pcv # Noop)
          (CMISS: ~ cache_hit c (opCodeToZ OpNoop) (__,__,__) pcl)
          (CUPD: c' = build_cache (opCodeToZ OpNoop) (__,__,__)  pcl),
    cstep (CState c m fh i s (pcv,pcl) false) 
          None (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_nop_p : forall c m fh i s pcv pcl,
    fh @ pcv # Noop ->
    cstep (CState c m fh i s (pcv,pcl) true) None (CState c m fh i s (pcv+1,pcl) true)

| cstep_add: forall c fh m i s rpcl pcv pcl rl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Add)
         (CHIT: cache_hit c (opCodeToZ OpAdd) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           None (CState c m fh i          ((x1v+x2v,rl):::s) (pcv+1,rpcl) false)

| cstep_add_f: forall c c' fh m i s pcv pcl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Add)
         (CMISS: ~ cache_hit c (opCodeToZ OpAdd) (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache (opCodeToZ OpAdd) (x1l,x2l,__)  pcl),
     cstep (CState c  m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           None (CState c' m fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_add_p: forall c m fh i s pcv pcl x1v x1l x2v x2l, 
    fh @ pcv # Add ->
    cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)  
          None (CState c m fh i ((x1v+x2v,handlerTag):::s) (pcv+1,pcl) true)

| cstep_sub: forall c fh m i s rpcl pcv  pcl rl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Sub)
         (CHIT: cache_hit c (opCodeToZ OpSub) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           None (CState c m fh i          ((x1v-x2v,rl):::s) (pcv+1,rpcl) false)

| cstep_sub_f: forall c c' fh m i s pcv pcl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Sub)
         (CMISS: ~ cache_hit c (opCodeToZ OpSub) (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache (opCodeToZ OpSub) (x1l,x2l,__)  pcl),
     cstep (CState c  m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           None (CState c' m fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_sub_p: forall c m fh i s pcv pcl x1v x1l x2v x2l, 
    fh @ pcv # Sub ->
    cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true) 
          None (CState c m fh i ((x1v-x2v,handlerTag):::s) (pcv+1,pcl) true)

| cstep_push: forall c fh m i s rpcl pcv pcl rl cv,
   forall(INST: i @ pcv # Push cv)
         (CHIT: cache_hit c (opCodeToZ OpPush) (__ , __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i s (pcv,pcl)   false)
           None (CState c m fh i ((cv,rl):::s) (pcv+1,rpcl) false)

| cstep_push_f: forall c c' fh m i s pcv pcl cv,
   forall(INST : i @ pcv # Push cv)
         (CMISS: ~ cache_hit c (opCodeToZ OpPush) (__,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpPush) (__,__,__) pcl),
     cstep (CState c  m fh i s (pcv,pcl) false)  
           None (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_push_p: forall c m fh i s pcv pcl cv, 
    fh @ pcv # Push cv ->
    cstep (CState c m fh i s (pcv,pcl) true) 
          None (CState c m fh i ((cv,handlerTag):::s) (pcv+1,pcl) true)

| cstep_load: forall c fh m i s rpcl pcv pcl rl addrv addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CHIT: cache_hit c (opCodeToZ OpLoad) (addrl, xl, __) pcl)
         (CREAD: cache_hit_read c rl rpcl)
         (MREAD: read_m addrv m = Some (xv,xl)),
     cstep (CState c m fh i ((addrv,addrl):::s) (pcv,pcl)   false)
           None (CState c m fh i ((xv,rl):::s) (pcv+1,rpcl) false)

| cstep_load_f: forall c c' fh m i s pcv pcl addrv addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CMISS: ~ cache_hit c (opCodeToZ OpLoad) (addrl,xl,__) pcl)
         (MREAD: read_m addrv m = Some (xv,xl))
         (CUPD : c' = build_cache (opCodeToZ OpLoad) (addrl,xl,__) pcl),
     cstep (CState c  m fh i ((addrv,addrl):::s) (pcv,pcl)   false)
           None (CState c' m fh i ((fh_ret pcv pcl)::(addrv,addrl):::s) fh_start true)

| cstep_load_p: forall c m fh i s pcv pcl addrv addrl xv xl,
    fh @ pcv # Load ->
    read_m addrv c = Some (xv,xl) ->
    cstep (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) true) 
          None (CState c m fh i ((xv,handlerTag):::s) (pcv+1,pcl) true)

| cstep_store: forall c fh m m' i s rpcl pcv pcl rl addrv addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CHIT: cache_hit c (opCodeToZ OpStore) (addrl, xl, ml) pcl)
         (CREAD: cache_hit_read c rl rpcl)
         (MREAD: read_m addrv m = Some (mv,ml))
         (MUPDT: upd_m addrv (xv,rl) m = Some m'),
     cstep (CState c m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           None (CState c m' fh i s (pcv+1,rpcl) false)

| cstep_store_f: forall c c' fh m i s pcv pcl addrv addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CMISS: ~ cache_hit c (opCodeToZ OpStore) (addrl,xl,ml) pcl)
         (MREAD: read_m addrv m = Some (mv,ml))
         (CUPD : c' = build_cache (opCodeToZ OpStore) (addrl,xl,ml) pcl),
     cstep (CState c  m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           None (CState c' m fh i ((fh_ret pcv pcl)::(addrv,addrl):::(xv,xl):::s) fh_start true)

| cstep_store_p: forall c m fh i s pcv pcl c' addrv addrl x, 
    fh @ pcv # Store ->
    upd_m addrv x c = Some c' ->
    cstep (CState c m fh i ((addrv,addrl)::: x :::s) (pcv,pcl) true)
          None (CState c' m fh i s (pcv+1,pcl) true)

| cstep_jump: forall c fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Jump)
         (CHIT: cache_hit c (opCodeToZ OpJump) (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((cv,cl):::s) (pcv,pcl)   false)
           None (CState c m fh i s (cv,rpcl) false)

| cstep_jump_f: forall c c' fh m i s pcv pcl cv cl,
   forall(INST: i @ pcv # Jump)
         (CMISS: ~ cache_hit c (opCodeToZ OpJump) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpJump) (cl,__,__) pcl),
     cstep (CState c  m fh i ((cv,cl):::s) (pcv,pcl)   false)
           None (CState c' m fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_jump_p: forall c m fh i s pcv pcl pcj pcjl,
    fh @ pcv # Jump ->
    cstep (CState c m fh i ((pcj,pcjl):::s) (pcv,pcl) true) 
          None (CState c m fh i s (pcj,pcjl) true)

| cstep_bnz: forall c fh m i s rpcl pcv pcl rl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CHIT: cache_hit c (opCodeToZ OpBranchNZ) (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((cv,cl):::s) (pcv,pcl)   false)
           None (CState c m fh i s (if cv =? 0 then pcv+1 else pcv+offv, rpcl) false)

| cstep_bnz_f: forall c c' fh m i s pcv pcl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CMISS: ~ cache_hit c (opCodeToZ OpBranchNZ) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpBranchNZ) (cl,__,__) pcl),
     cstep (CState c  m fh i ((cv,cl):::s) (pcv,pcl)   false)
           None (CState c' m fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_branchnz_p: forall c m fh i s pcv pcl offv av al,
    fh @ pcv # BranchNZ offv -> 
    cstep (CState c m fh i ((av,al):::s) (pcv,pcl) true) 
          None (CState c m fh i s (if av =? 0 then pcv+1 else pcv+offv, handlerTag) true)

| cstep_call: forall c fh m i s rpcl pcv pcl rl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGSA: length args = a) 
         (ARGS: forall a, In a args -> exists d, a = CData d)
         (CHIT: cache_hit c (opCodeToZ OpCall) (pccl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl)   false)
           None (CState c m fh i (args++(((CRet (pcv+1, rl)) r false)::s)) (pcc,rpcl) false)

| cstep_call_f: forall c c' fh m i s pcv pcl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGSA: length args = a) 
         (ARGS: forall a, In a args -> exists d, a = CData d)
         (CMISS: ~ cache_hit c (opCodeToZ OpCall) (pccl, __, __) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpCall) (pccl,__,__) pcl),
     cstep (CState c  m fh i ((pcc,pccl):::args++s) (pcv,pcl)   false)
           None (CState c' m fh i ((fh_ret pcv pcl)::(pcc,pccl):::args++s) fh_start true)

| cstep_call_p: forall c m fh i s pcv pcl a r args pcc pccl,
    fh @ pcv # Call a r -> 
    length args = a -> (forall a, In a args -> exists d, a = CData d) ->
    cstep (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl) true) 
          None (CState c m fh i (args++(CRet (pcv+1, pcl) r true)::s) (pcc, pccl) true)

| cstep_ret: forall c fh m i s s' pcv pcl rl rpcl pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CHIT: cache_hit c (opCodeToZ OpRet) (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false false)::s')) 
                (*DD: should only return to user mode *)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i s  (pcv,pcl) false)
           None (CState c m fh i s' (pcret, rpcl) false)

| cstep_ret_f: forall c c' fh m i s' s pcv pcl pret pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CMISS: ~ cache_hit c (opCodeToZ OpRet) (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s')) 
         (*DD: same thing, but we need not to constraint the return
               mode here, actually. *)
         (CUPD : c' = build_cache (opCodeToZ OpRet) (pcretl,__,__) pcl),
     cstep (CState c m fh i s  (pcv,pcl) false)
           None (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_ret_p: forall c m fh i s pcv pcl  pcret pcretl s' pret, 
    fh @ pcv # Ret -> (* can either return to user/priv mode *)
    c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s') ->
    cstep (CState c m fh i s  (pcv,pcl) true) 
          None (CState c m fh i s' (pcret,pcretl) pret)

| cstep_vret: forall c fh m i s s' pcv pcl rl rpcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CHIT: cache_hit c (opCodeToZ OpVRet) (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) true false)::s')) 
                (*DD: should only return to user mode *)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((resv,resl):::s)  (pcv,pcl) false)
           None (CState c m fh i ((resv,rl):::s') (pcret,rpcl) false)

| cstep_vret_f: forall c c' fh m i s' s pcv pcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CMISS: ~ cache_hit c (opCodeToZ OpVRet) (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) true false)::s')) (*DD: same thing *)
         (CUPD : c' = build_cache (opCodeToZ OpVRet) (resl,pcretl,__) pcl),
     cstep (CState c m fh i ((resv,resl):::s)  (pcv,pcl) false)
           None (CState c' m fh i ((fh_ret pcv pcl)::(resv,resl):::s) fh_start true)

| cstep_vret_p: forall c m fh i s pcv pcl s' pcret pcretl resv resl, 
    fh @ pcv # VRet -> (* cannot vreturn to user mode *)
    c_pop_to_return s ((CRet (pcret,pcretl) true true)::s') ->
    cstep (CState c m fh i ((resv,resl):::s) (pcv,pcl) true) 
          None (CState c m fh i ((resv,resl):::s') (pcret, pcretl) true)

| cstep_out: forall c fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Output)
         (CHIT: cache_hit c (opCodeToZ OpOutput) (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((cv,cl):::s) (pcv,pcl)   false)
           (Some (CEInt (cv,rl))) (CState c m fh i s (pcv+1,rpcl) false)

| cstep_out_f: forall c c' fh m i s pcv pcl cv cl,
   forall(INST: i @ pcv # Output)
         (CMISS: ~ cache_hit c (opCodeToZ OpOutput) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpOutput) (cl,__,__) pcl),
     cstep (CState c  m fh i ((cv,cl):::s) (pcv,pcl)   false)
           None (CState c' m fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true).

(* Success is reaching a Halt state in non-privileged mode and valid address. *)
Definition c_success (cs : CS) : Prop :=
  match index_list_Z (fst (pc cs)) (imem cs) with
  | Some Halt => is_true (negb (priv cs))
  | _ => False
  end.

End CMach.
