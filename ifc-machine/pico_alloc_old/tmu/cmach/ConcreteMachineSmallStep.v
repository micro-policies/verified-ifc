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
Notation fh_ret := (fun pc pcl => (CRet (Vint pc,pcl) false false)).

(** Concrete machine transition relation.
    Each instructions has 3 semantic rules: (user mode - succ) (user mode - faulting) (kernel mode) *)

(* DP: to be moved in Concrete.v *)
Definition mem := Mem.t (@Atom Z).
Definition cache_hit_mem (m:mem) (opcode:Z) (tags: Z * Z * Z) (pctags:Z) : Prop :=
  match Mem.get_frame m Mem.cblock with
    | None => False
    | Some c => cache_hit c opcode tags pctags
  end.

Definition cache_hit_read_mem (m:mem) (tagr:Z) (tagrpc:Z) : Prop :=
  match Mem.get_frame m Mem.cblock with
    | None => False
    | Some c => cache_hit_read c tagr tagrpc
  end.

Inductive cstep : CS -> option CEvent -> CS -> Prop := 
| cstep_nop : forall m fh i s pcv pcl rl rpcl,
    forall (INST: i @ pcv # Noop)
           (CHIT: cache_hit_mem m (opCodeToZ OpNoop) (__,__,__) pcl)
           (CREAD: cache_hit_read_mem m rl rpcl),
    cstep (CState m fh i s (pcv,pcl) false)
          None (CState m fh i s (pcv+1,rpcl) false)

| cstep_nop_f : forall c' m fh i s pcv pcl,
   forall (INST: i @ pcv # Noop)
          (CMISS: ~ cache_hit_mem m (opCodeToZ OpNoop) (__,__,__) pcl)
          (CUPD: c' = build_cache (opCodeToZ OpNoop) (__,__,__)  pcl),
    cstep (CState m fh i s (pcv,pcl) false) 
          None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_nop_p : forall m fh i s pcv pcl,
    fh @ pcv # Noop ->
    cstep (CState m fh i s (pcv,pcl) true) None (CState m fh i s (pcv+1,pcl) true)

| cstep_add: forall fh m i s rpcl pcv pcl rl x1v x1l x2v x2l v,
   forall(INST: i @ pcv # Add)
         (CHIT: cache_hit_mem m (opCodeToZ OpAdd) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl)
         (ADD: add x1v x2v = Some v),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           None (CState m fh i          ((v,rl):::s) (pcv+1,rpcl) false)

| cstep_add_f: forall c' fh m i s pcv pcl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Add)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpAdd) (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache (opCodeToZ OpAdd) (x1l,x2l,__)  pcl),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_add_p: forall m fh i s pcv pcl x1v x1l x2v x2l v, 
    fh @ pcv # Add ->
    add x1v x2v = Some v ->
    cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)  
          None (CState m fh i ((v,handlerTag):::s) (pcv+1,pcl) true)

| cstep_sub: forall fh m i s rpcl pcv  pcl rl x1v x1l x2v x2l v,
   forall(INST: i @ pcv # Sub)
         (CHIT: cache_hit_mem m (opCodeToZ OpSub) (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl)
         (SUB: sub x1v x2v = Some v),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           None (CState m fh i          ((v,rl):::s) (pcv+1,rpcl) false)

| cstep_sub_f: forall c' fh m i s pcv pcl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Sub)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpSub) (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache (opCodeToZ OpSub) (x1l,x2l,__)  pcl),
     cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_sub_p: forall m fh i s pcv pcl x1v x1l x2v x2l v, 
    fh @ pcv # Sub ->
    sub x1v x2v = Some v ->
    cstep (CState m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true) 
          None (CState m fh i ((v,handlerTag):::s) (pcv+1,pcl) true)

| cstep_push: forall fh m i s rpcl pcv pcl rl cv,
   forall(INST: i @ pcv # Push cv)
         (CHIT: cache_hit_mem m (opCodeToZ OpPush) (__ , __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i s (pcv,pcl)   false)
           None (CState m fh i ((Vint cv,rl):::s) (pcv+1,rpcl) false)

| cstep_push_f: forall c' fh m i s pcv pcl cv,
   forall(INST : i @ pcv # Push cv)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpPush) (__,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpPush) (__,__,__) pcl),
     cstep (CState m fh i s (pcv,pcl) false)  
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_push_p: forall m fh i s pcv pcl cv, 
    fh @ pcv # Push cv ->
    cstep (CState m fh i s (pcv,pcl) true) 
          None (CState m fh i ((Vint cv,handlerTag):::s) (pcv+1,pcl) true)

| cstep_push_cache_ptr_p: forall m fh i s pcv pcl, 
    fh @ pcv # PushCachePtr ->
    cstep (CState m fh i s (pcv,pcl) true) 
          None (CState m fh i ((Vptr Mem.cblock 0,handlerTag):::s) (pcv+1,pcl) true)

| cstep_load: forall fh m i s rpcl pcv pcl rl b ofs addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CHIT: cache_hit_mem m (opCodeToZ OpLoad) (addrl, xl, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl)
         (MREAD: Mem.load b ofs m = Some (xv,xl))
         (PRIV: Mem.privilege_bit b = User),
     cstep (CState m fh i ((Vptr b ofs,addrl):::s) (pcv,pcl)   false)
           None (CState m fh i ((xv,rl):::s) (pcv+1,rpcl) false)

| cstep_load_f: forall c' fh m i s pcv pcl b ofs addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpLoad) (addrl,xl,__) pcl)
         (MREAD: Mem.load b ofs m = Some (xv,xl))
         (CUPD : c' = build_cache (opCodeToZ OpLoad) (addrl,xl,__) pcl)
         (PRIV: Mem.privilege_bit b = User),
     cstep (CState m fh i ((Vptr b ofs,addrl):::s) (pcv,pcl)   false)
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::(Vptr b ofs,addrl):::s) fh_start true)

| cstep_load_p: forall m fh i s pcv pcl b ofs addrl xv xl,
   forall (INST: fh @ pcv # Load)
          (READ: Mem.load b ofs m = Some (xv,xl))
          (PRIV: Mem.privilege_bit b = Kernel),
    cstep (CState m fh i ((Vptr b ofs,addrl):::s) (pcv,pcl) true) 
          None (CState m fh i ((xv,handlerTag):::s) (pcv+1,pcl) true)

| cstep_store: forall fh m m' i s rpcl pcv pcl rl b ofs addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CHIT: cache_hit_mem m (opCodeToZ OpStore) (addrl, xl, ml) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl)
         (MREAD: Mem.load b ofs m = Some (mv,ml))
         (MUPDT: Mem.store b ofs (xv,rl) m = Some m')
         (PRIV: Mem.privilege_bit b = User),
     cstep (CState m fh i ((Vptr b ofs,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           None (CState m' fh i s (pcv+1,rpcl) false)

| cstep_store_f: forall c' fh m i s pcv pcl b ofs addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpStore) (addrl,xl,ml) pcl)
         (MREAD: Mem.load b ofs m = Some (mv,ml))
         (CUPD : c' = build_cache (opCodeToZ OpStore) (addrl,xl,ml) pcl)
         (PRIV: Mem.privilege_bit b = User),
     cstep (CState m fh i ((Vptr b ofs,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::(Vptr b ofs,addrl):::(xv,xl):::s) fh_start true)

| cstep_store_p: forall m fh i s pcv pcl m' b ofs addrl x, 
    forall (INST:fh @ pcv # Store)
           (UPD: Mem.store b ofs x m = Some m')
           (PRIV: Mem.privilege_bit b = Kernel),
    cstep (CState m fh i ((Vptr b ofs,addrl)::: x :::s) (pcv,pcl) true)
          None (CState m' fh i s (pcv+1,pcl) true)

| cstep_jump: forall fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Jump)
         (CHIT: cache_hit_mem m (opCodeToZ OpJump) (cl, __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((Vint cv,cl):::s) (pcv,pcl)   false)
           None (CState m fh i s (cv,rpcl) false)

| cstep_jump_f: forall c' fh m i s pcv pcl cv cl,
   forall(INST: i @ pcv # Jump)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpJump) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpJump) (cl,__,__) pcl),
     cstep (CState m fh i ((cv,cl):::s) (pcv,pcl)   false)
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_jump_p: forall m fh i s pcv pcl pcj pcjl,
    forall (INST: fh @ pcv # Jump),
    cstep (CState m fh i ((Vint pcj,pcjl):::s) (pcv,pcl) true) 
          None (CState m fh i s (pcj,pcjl) true)

| cstep_bnz: forall fh m i s rpcl pcv pcl rl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CHIT: cache_hit_mem m (opCodeToZ OpBranchNZ) (cl, __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((Vint cv,cl):::s) (pcv,pcl)   false)
           None (CState m fh i s (if cv =? 0 then pcv+1 else pcv+offv, rpcl) false)

| cstep_bnz_f: forall c' fh m i s pcv pcl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpBranchNZ) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpBranchNZ) (cl,__,__) pcl),
     cstep (CState m fh i ((Vint cv,cl):::s) (pcv,pcl)   false)
           None (CState m fh i ((fh_ret pcv pcl)::(Vint cv,cl):::s) fh_start true)

| cstep_branchnz_p: forall m fh i s pcv pcl offv av al,
    forall (INST: fh @ pcv # BranchNZ offv),
    cstep (CState m fh i ((Vint av,al):::s) (pcv,pcl) true) 
          None (CState m fh i s (if av =? 0 then pcv+1 else pcv+offv, handlerTag) true)

| cstep_call: forall fh m i s rpcl pcv pcl rl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGSA: length args = a) 
         (ARGS: forall a, In a args -> exists d, a = CData d)
         (CHIT: cache_hit_mem m (opCodeToZ OpCall) (pccl, __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((Vint pcc,pccl):::args++s) (pcv,pcl)   false)
           None (CState m fh i (args++(((CRet (Vint (pcv+1), rl)) r false)::s)) (pcc,rpcl) false)

| cstep_call_f: forall c' fh m i s pcv pcl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGSA: length args = a) 
         (ARGS: forall a, In a args -> exists d, a = CData d)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpCall) (pccl, __, __) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpCall) (pccl,__,__) pcl),
     cstep (CState m fh i ((pcc,pccl):::args++s) (pcv,pcl)   false)
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::(pcc,pccl):::args++s) fh_start true)

| cstep_call_p: forall m fh i s pcv pcl a r args pcc pccl,
    forall (INST: fh @ pcv # Call a r)
           (ARGSA: length args = a)
           (ARGS: forall a, In a args -> exists d, a = CData d),
    cstep (CState m fh i ((Vint pcc,pccl):::args++s) (pcv,pcl) true) 
          None (CState m fh i (args++(CRet (Vint (pcv+1), pcl) r true)::s) (pcc, pccl) true)

| cstep_ret: forall fh m i s s' pcv pcl rl rpcl pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CHIT: cache_hit_mem m (opCodeToZ OpRet) (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (Vint pcret,pcretl) false false)::s')) 
                (*DD: should only return to user mode *)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i s  (pcv,pcl) false)
           None (CState m fh i s' (pcret, rpcl) false)

| cstep_ret_f: forall c' fh m i s' s pcv pcl pret pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpRet) (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (Vint pcret,pcretl) false pret)::s')) 
         (*DD: same thing, but we need not to constraint the return
               mode here, actually. *)
         (CUPD : c' = build_cache (opCodeToZ OpRet) (pcretl,__,__) pcl),
     cstep (CState m fh i s  (pcv,pcl) false)
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_ret_p: forall m fh i s pcv pcl  pcret pcretl s' pret, 
    forall (INST: fh @ pcv # Ret) (* can either return to user/priv mode *)
           (POP: c_pop_to_return s ((CRet (Vint pcret,pcretl) false pret)::s')),
    cstep (CState m fh i s  (pcv,pcl) true) 
          None (CState m fh i s' (pcret,pcretl) pret)

| cstep_vret: forall fh m i s s' pcv pcl rl rpcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CHIT: cache_hit_mem m (opCodeToZ OpVRet) (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (Vint pcret,pcretl) true false)::s')) 
                (*DD: should only return to user mode *)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((resv,resl):::s)  (pcv,pcl) false)
           None (CState m fh i ((resv,rl):::s') (pcret,rpcl) false)

| cstep_vret_f: forall c' fh m i s' s pcv pcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpVRet) (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (Vint pcret,pcretl) true false)::s')) (*DD: same thing *)
         (CUPD : c' = build_cache (opCodeToZ OpVRet) (resl,pcretl,__) pcl),
     cstep (CState m fh i ((resv,resl):::s)  (pcv,pcl) false)
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::(resv,resl):::s) fh_start true)

| cstep_vret_p: forall m fh i s pcv pcl s' pcret pcretl resv resl, 
    forall (INST: fh @ pcv # VRet) (* cannot vreturn to user mode *)
           (POP: c_pop_to_return s ((CRet (Vint pcret,pcretl) true true)::s')),
    cstep (CState m fh i ((resv,resl):::s) (pcv,pcl) true) 
          None (CState m fh i ((resv,resl):::s') (pcret, pcretl) true)

| cstep_out: forall fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Output)
         (CHIT: cache_hit_mem m (opCodeToZ OpOutput) (cl, __, __) pcl)
         (CREAD: cache_hit_read_mem m rl rpcl),
     cstep (CState m fh i ((cv,cl):::s) (pcv,pcl)   false)
           (Some (CEInt (cv,rl))) (CState m fh i s (pcv+1,rpcl) false)

| cstep_out_f: forall c' fh m i s pcv pcl cv cl,
   forall(INST: i @ pcv # Output)
         (CMISS: ~ cache_hit_mem m (opCodeToZ OpOutput) (cl,__,__) pcl)
         (CUPD : c' = build_cache (opCodeToZ OpOutput) (cl,__,__) pcl),
     cstep (CState m fh i ((cv,cl):::s) (pcv,pcl)   false)
           None (CState (Mem.cupd m c') fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true).

(* Success is reaching a Halt state in non-privileged mode and valid address. *)
Definition c_success (cs : CS) : Prop :=
  match index_list_Z (fst (pc cs)) (imem cs) with
  | Some Halt => is_true (negb (priv cs))
  | _ => False
  end.

Inductive runsToEscape : CS -> list CEvent -> CS -> Prop :=
| rte_success: (* executing until a return to user mode *)
    forall cs cs' t,
    forall (PRIV:  priv cs = true)
           (STAR:  star cstep cs t cs')
           (UPRIV: priv cs' = false), 
      runsToEscape cs t cs'
| rte_fail : (* executing the tmu until it fails at a neg. pc in priv mode *)
    forall cs cs' t,
    forall (PRIV: priv cs = true)
           (STAR: star cstep cs t cs')
           (PRIV: priv cs' = true)
           (FAIL: fst (pc cs') < 0), 
      runsToEscape cs t cs'
| rte_upriv: (* in unpriv. mode, it already escaped *) 
    forall cs,
    forall (UPRIV: priv cs = false),
      runsToEscape cs nil cs.

Lemma step_star_plus (S E: Type): 
  forall (Rstep: S -> option E -> S -> Prop) (s2 s3: S) t, 
    star Rstep s2 t s3 ->
    forall s1 e t', 
      Rstep s1 e s2 ->
      t' = (op_cons e t) ->
      plus Rstep s1 t' s3.
Proof.
  induction 1; intros; eauto.
Qed.

Lemma runsToEscape_plus: forall s1 s2 t,
 runsToEscape s1 t s2 ->
 s1 <> s2 ->
 plus cstep s1 t s2.
Proof.
  induction 1 ; intros;
  try ( inv STAR; [ congruence | eapply step_star_plus; eauto]).
  congruence.
Qed.

Lemma runsToEscape_star: forall s1 s2 t,
 runsToEscape s1 t s2 ->
 star cstep s1 t s2.
Proof.
  inversion 1; eauto.
Qed.

Lemma star_trans: forall S E (Rstep: S -> option E -> S -> Prop) s0 t s1,
  star Rstep s0 t s1 ->
  forall t' s2,
  star Rstep s1 t' s2 ->
  star Rstep s0 (t++t') s2.
Proof.
  induction 1.
  - auto.
  - inversion 1.
    + rewrite app_nil_r.
      subst; econstructor; eauto.
    + subst; econstructor; eauto.
      rewrite op_cons_app; reflexivity.
Qed.

End CMach.
