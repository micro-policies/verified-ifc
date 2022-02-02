Require Import List.
Require Import ZArith.
Require Import Lia.

Require Import Utils.
Require Import Lattices.

Require Import Instr Memory.
Require Import Semantics.
Require Import AbstractCommon.
Require Import Rules.

Require Coq.Vectors.Vector.

Set Implicit Arguments.

Definition labelCount (c:OpCode) : nat :=
match c with
| OpNoop => 0
| OpAdd  => 2
| OpSub  => 2
| OpEq   => 2
| OpDup  => 1
| OpSwap => 0
| OpPush => 0
| OpPop => 0
| OpAlloc => 1
| OpLoad => 2
| OpStore => 3
| OpJump => 1
| OpBranchNZ => 1
| OpCall => 1
| OpRet => 1
| OpVRet => 2
| OpOutput => 1
| OpSizeOf => 1
| OpGetOff => 1
end.

Lemma labelCountBounds : forall opcode, labelCount opcode <= 3.
Proof. intros. destruct opcode; simpl; lia. Qed.

Local Open Scope Z_scope.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

(** * Rules of the abstract machine *)
(** Get the "rule" for a given operation. *)
Variable fetch_rule : forall opcode : OpCode, AllowModify (labelCount opcode).

Variable table : ASysTable T.

Definition qa_state := AS T unit.
Definition qa_alloc
      (size:Z) (a:Atom T unit) (m:memory T unit): option (block unit * memory T unit) :=
  alloc Global tt size a m.

(** run_tmr (TMR for Tag Managment Rules): fetches the rule for the
   given opcode and applies it.  *)

Definition run_tmr (opcode: OpCode) (pclab: T) (vlabs:Vector.t T (labelCount opcode)) :  option (T * T) :=
  let r := (fetch_rule opcode) in
  apply_rule r pclab vlabs.

Inductive step_rules : qa_state -> (@Event T)+τ -> qa_state -> Prop :=
| step_nop : forall m i s pcv pcl rpcl rl,
    index_list_Z pcv i = Some Noop ->
    run_tmr OpNoop pcl <||> = Some (rpcl,rl) ->
    step_rules (AState m i s (pcv,pcl)) Silent (AState m i s (pcv+1,rpcl))

| step_add: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l xv,
    index_list_Z pcv i = Some Add ->
    add x1v x2v = Some xv ->
    run_tmr OpAdd pcl <|x1l;x2l|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               Silent
               (AState m i ((AData (xv,rl))::s) (pcv+1,rpcl))

| step_sub: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l xv,
    index_list_Z pcv i = Some Sub ->
    sub x1v x2v = Some xv ->
    run_tmr OpSub pcl <|x1l;x2l|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               Silent
               (AState m i ((AData (xv,rl))::s) (pcv+1,rpcl))

| step_eq: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l,
    index_list_Z pcv i = Some Eq ->
    run_tmr OpEq pcl <|x1l;x2l|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl))
               Silent
               (AState m i ((AData (val_eq x1v x2v,rl))::s) (pcv+1,rpcl))

| step_dup : forall m i s1 s2 pcv pcl n xv xl rpcl rl
    (INSTR: index_list_Z pcv i = Some (Dup n))
    (IDX: index_list n s1 = Some (AData (xv, xl)))
    (DATA: forall se, In se s1 -> exists a, se = AData a)
    (TMU: run_tmr OpDup pcl <|xl|> = Some (rpcl,rl)),
    step_rules (AState m i (s1 ++ s2) (pcv, pcl))
               Silent
               (AState m i (AData (xv, rl) :: s1 ++ s2) (pcv+1,rpcl))

| step_swap : forall m i s1 s1' s2 pcv pcl n rpcl rl
    (INSTR: index_list_Z pcv i = Some (Swap n))
    (SWAP: swap n s1 = Some s1')
    (DATA: forall se, In se s1 -> exists a, se = AData a)
    (TMU: run_tmr OpSwap pcl <||> = Some (rpcl,rl)),
    step_rules (AState m i (s1 ++ s2) (pcv, pcl))
               Silent
               (AState m i (s1' ++ s2) (pcv+1,rpcl))

| step_push: forall m i s pcv pcl rpcl rl cv,
    index_list_Z pcv i = Some (Push cv) ->
    run_tmr OpPush pcl <||> = Some (rpcl,rl) ->
    step_rules (AState m i s (pcv,pcl))
               Silent
               (AState m i ((AData (Vint cv,rl))::s) (pcv+1,rpcl))

| step_pop: forall m i s pcv pcl rpcl rl a,
    index_list_Z pcv i = Some Pop ->
    run_tmr OpPop pcl <||> = Some (rpcl,rl) ->
    step_rules (AState m i (AData a :: s) (pcv,pcl))
               Silent
               (AState m i s (pcv+1,rpcl))

| step_alloc: forall m i s pcv pcl b size sizel xv xl m' rpcl rl,
    index_list_Z pcv i = Some Alloc ->
    run_tmr OpAlloc pcl <|sizel|> = Some (rpcl,rl) ->
    qa_alloc size (xv,xl) m = Some (b,m') ->
    step_rules (AState m i (AData (Vint size,sizel)::AData (xv,xl)::s) (pcv,pcl))
               Silent
               (AState m' i (AData (Vptr (b, 0),rl)::s) (pcv+1,rpcl))

| step_load: forall m i s pcv pcl p addrl xv xl rl rpcl,
    index_list_Z pcv i = Some Load ->
    load p m = Some (xv,xl) ->
    run_tmr OpLoad pcl <|addrl;xl|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (Vptr p,addrl))::s) (pcv,pcl))
               Silent
               (AState m i ((AData (xv, rl))::s) (pcv+1,rpcl))

| step_store: forall m i s pcv pcl p addrl xv xl mv ml rl rpcl m',
    index_list_Z pcv i = Some Store ->
    load p m = Some (mv,ml) ->
    store p (xv,rl) m = Some m' ->
    run_tmr OpStore pcl <|addrl;xl;ml|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (Vptr p,addrl))::(AData (xv,xl))::s) (pcv,pcl))
               Silent
               (AState m' i s (pcv+1,rpcl))

| step_jump: forall m i s pcv pcl pcv' pcl' rl rpcl,
    index_list_Z pcv i = Some Jump ->
    run_tmr OpJump pcl <|pcl'|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (Vint pcv',pcl'))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv',rpcl))

| step_branchnz_true: forall m i s pcv pcl offv al rl rpcl,
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    run_tmr OpBranchNZ pcl <|al|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (Vint 0,al))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv+1,rpcl))

| step_branchnz_false: forall m i s pcv pcl offv av al rl rpcl,
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    run_tmr OpBranchNZ pcl <|al|> = Some (rpcl,rl) ->
    av <> 0 ->
    step_rules (AState m i ((AData (Vint av,al))::s) (pcv,pcl))
               Silent
               (AState m i s (pcv+offv,rpcl))

| step_call: forall m i s pcv pcl pcv' pcl' rl rpcl args a r,
    index_list_Z pcv i = Some (Call a r) ->
    run_tmr OpCall pcl <|pcl'|> = Some (rpcl,rl) ->
    length args = a ->
    (forall a, In a args -> exists d, a = AData d) ->
    step_rules (AState m i ((AData (Vint pcv',pcl'))::args++s) (pcv,pcl))
               Silent
               (AState m i (args++(ARet (pcv+1,rl) r)::s) (pcv',rpcl))

| step_ret: forall m i s pcv pcl pcv' pcl' rl rpcl s' ,
    index_list_Z pcv i = Some Ret ->
    pop_to_return s ((ARet (pcv',pcl') false)::s') ->
    run_tmr OpRet pcl <|pcl'|> = Some (rpcl,rl) ->
    step_rules (AState m i s  (pcv,pcl)) Silent (AState m i s' (pcv',rpcl))

| step_vret: forall m i s pcv pcl pcv' pcl' rl rpcl resv resl s' ,
    index_list_Z pcv i = Some VRet ->
    pop_to_return s ((ARet (pcv',pcl') true)::s') ->
    run_tmr OpVRet pcl <|resl;pcl'|> = Some (rpcl,rl) ->
    step_rules (AState m i (AData (resv,resl)::s) (pcv,pcl))
               Silent (AState m i (AData (resv, rl)::s') (pcv',rpcl))

| step_output: forall m i s pcv pcl rl rpcl xv xl,
    index_list_Z pcv i = Some Output ->
    run_tmr OpOutput pcl <|xl|> = Some (rpcl,rl) ->
    step_rules (AState m i (AData (Vint xv,xl)::s) (pcv,pcl))
               (E (EInt (xv,rl))) (AState m i s (pcv+1,rpcl))

| step_syscall: forall id m i s pcv pcl args res sys_info
    (INSTR: index_list_Z pcv i = Some (SysCall id))
    (SYS: table id = Some sys_info)
    (SYSLENGTH: length args = sys_info.(asi_arity))
    (SYSSEM: sys_info.(asi_sem) args = Some res), (* this encodes potential IFC check failures *)
    step_rules (AState m i (map AData args ++ s) (pcv,pcl))
               Silent (AState m i (AData res :: s) (pcv+1,pcl))

| step_sizeof: forall m i s pcv pcl p pl fr rpcl rl
    (INSTR: index_list_Z pcv i = Some SizeOf)
    (FRAME: Mem.get_frame m (fst p) = Some fr)
    (TMU: run_tmr OpSizeOf pcl <|pl|> = Some (rpcl,rl)),
    step_rules (AState m i (AData (Vptr p, pl)::s) (pcv,pcl))
               Silent (AState m i (AData (Vint (Z.of_nat (length fr)), rl)::s) (pcv+1,rpcl))

| step_getoff: forall m i s pcv pcl p pl rpcl rl
    (INSTR: index_list_Z pcv i = Some GetOff)
    (TMU: run_tmr OpGetOff pcl <|pl|> = Some (rpcl,rl)),
    step_rules (AState m i (AData (Vptr p, pl)::s) (pcv,pcl))
               Silent (AState m i (AData (Vint (snd p), rl)::s) (pcv+1,rpcl)).

Definition quasi_abstract_machine :=
  {| state := qa_state ;
     event := (Event T);
     step := step_rules ;
     init_data := abstract_init_data T;
     init_state := fun id =>
                     let '(p,d,def) := id in
                     {| amem := Mem.empty _ _;
                        aimem := p ;
                        astk := map (fun a: Z*T => let (i,l) := a in AData (Vint i, l)) d;
                        apc := (0%Z, def) |}
  |}.

End ARuleMachine.

Section IfcQuasiAbstractMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Variable table : ASysTable T.

Definition fetch_rule (opcode:OpCode) : (AllowModify (labelCount opcode)) :=
  match opcode with
    | OpNoop => ≪ TRUE , LabPC , __ ≫
    | OpAdd => ≪ TRUE,  LabPC , JOIN Lab1 Lab2 ≫
    | OpSub => ≪ TRUE, LabPC, JOIN Lab1 Lab2 ≫
    | OpEq => ≪ TRUE, LabPC, JOIN Lab1 Lab2 ≫
    | OpDup => ≪ TRUE, LabPC, Lab1 ≫
    | OpSwap => ≪ TRUE, LabPC, BOT ≫
    | OpPush => ≪ TRUE, LabPC , BOT ≫
    | OpPop => ≪ TRUE, LabPC, BOT ≫
    | OpAlloc => ≪ TRUE, LabPC , Lab1 ≫
    | OpLoad => ≪ TRUE, LabPC, JOIN Lab1 Lab2 ≫
    | OpStore => ≪ LE (JOIN Lab1 LabPC) Lab3,  (* addr, new value, old value *)
                   LabPC ,
                  JOIN (JOIN Lab1 LabPC) Lab2 ≫
    | OpJump => ≪ TRUE, JOIN Lab1 LabPC , __ ≫
    | OpBranchNZ => ≪ TRUE, JOIN Lab1 LabPC , __ ≫
    | OpCall => ≪ TRUE , JOIN Lab1 LabPC , LabPC ≫
    | OpRet => ≪ TRUE, Lab1 , __ ≫
    | OpVRet => ≪ TRUE, Lab2 , JOIN Lab1 LabPC ≫ (* value, return addr *)
    | OpOutput => ≪ TRUE, LabPC , JOIN Lab1 LabPC ≫ (* output value *)
    | OpSizeOf => ≪ TRUE, LabPC , Lab1 ≫
    | OpGetOff => ≪ TRUE, LabPC , Lab1 ≫
    end.

Definition tini_quasi_abstract_machine := quasi_abstract_machine fetch_rule table.

Ltac step_tmr :=
  match goal with
    | [ H: run_tmr _ _ _ _ = _  |- _ ] => inv H
  end.

Lemma step_rules_non_ret_label_pc: forall m i stk pc l s instr e,
  step tini_quasi_abstract_machine (AState m i stk (pc, l)) e s ->
  index_list_Z pc i = Some instr ->
  instr <> Ret ->
  instr <> VRet ->
  exists (l' : T) (pc' : Z), apc s = (pc', l') /\ l <: l' = true.
Proof.
  intros. simpl in H.
  inv H; try step_tmr ; simpl in *; eauto.

  unfold run_tmr, apply_rule  in H3. simpl in H3.
  unfold Vector.nth_order in H3. simpl in H3.
  set (assert1 := addrl \_/ l <: ml) in *.
  case_eq assert1; intros;
  (unfold assert1 in * );
  (rewrite H in *; simpl in * ) ; allinv.
  eauto.

  congruence.
  congruence.
Qed.

End IfcQuasiAbstractMachine.
