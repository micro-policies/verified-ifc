(* Quasi-Abstract Machine. 
   Like the abstract machine, but IFC decisions are factored out into
   a separate rule evaluator. *)

Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.

Require Import Instr.
Require Import Semantics.
Require Import AbstractCommon.
Require Import Rules.

Require Vector.

Set Implicit Arguments.

Definition run_tmr_type (labelCount : OpCode -> nat) (T : Type) :=
  forall (opcode : OpCode)
         (pclab : T)
         (labs : Vector.t T (labelCount opcode)),
    option (T * T).

(* How many argument labels come with this OpCode ? *)
Definition labelCount (c:OpCode) : nat :=
match c with
| OpNoop => 0
| OpAdd  => 2
| OpSub  => 2
| OpPush => 0
| OpPop => 0
| OpLoad => 2
| OpStore => 3
| OpJump => 1
| OpBranchNZ => 1
| OpCall => 1
| OpRet => 1
| OpVRet => 2
| OpOutput => 1
end.

Local Open Scope Z_scope.

Section QAMachine.

Context {T: Type}.

(** * Rules of the abstract machine :  *)

(** The [run_tmr opcode pclab labs] should say if an instruction is
allowed to execute on a given combination of PC label ([pclab]) and
argument labels ([labs]). It should return [Some (rpcl, rl)] if
execution is allowed, where [rpcl] is the new PC label and [rl] is a
label for a possible result; otherwise, it should return [None] *)

Variable run_tmr : run_tmr_type labelCount T.

(** Step relation *)   
Inductive step_rules : @AS T -> (@Event T)+τ -> @AS T -> Prop := 
| step_nop : forall m i s pcv pcl rpcl rl,
    index_list_Z pcv i = Some Noop ->
    run_tmr OpNoop pcl <||> = Some (rpcl,rl) ->
    step_rules (AState m i s (pcv,pcl)) Silent (AState m i s (pcv+1,rpcl))

| step_add: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l, 
    index_list_Z pcv i = Some Add ->
    run_tmr OpAdd pcl <|x1l;x2l|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl)) 
               Silent
               (AState m i ((AData (x1v+x2v,rl))::s) (pcv+1,rpcl))

| step_sub: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l, 
    index_list_Z pcv i = Some Sub ->
    run_tmr OpSub pcl <|x1l;x2l|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl)) 
               Silent
               (AState m i ((AData (x1v-x2v,rl))::s) (pcv+1,rpcl))

| step_push: forall m i s pcv pcl rpcl rl cv,
    index_list_Z pcv i = Some (Push cv) ->
    run_tmr OpPush pcl <||> = Some (rpcl,rl) ->
    step_rules (AState m i s (pcv,pcl)) 
               Silent
               (AState m i ((AData (cv,rl))::s) (pcv+1,rpcl))

| step_pop: forall m i s pcv pcl rpcl rl a,
    index_list_Z pcv i = Some Pop ->
    run_tmr OpPop pcl <||> = Some (rpcl,rl) ->
    step_rules (AState m i (AData a :: s) (pcv,pcl))
               Silent
               (AState m i s (pcv+1,rpcl))

| step_load: forall m i s pcv pcl addrv addrl xv xl rl rpcl, 
    index_list_Z pcv i = Some Load ->
    index_list_Z addrv m = Some (xv,xl) ->
    run_tmr OpLoad pcl <|addrl;xl|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (addrv,addrl))::s) (pcv,pcl)) 
               Silent
               (AState m i ((AData (xv, rl))::s) (pcv+1,rpcl))

| step_store: forall m i s pcv pcl addrv addrl xv xl mv ml rl rpcl m', 
    index_list_Z pcv i = Some Store ->
    index_list_Z addrv m = Some (mv,ml) ->
    update_list_Z addrv (xv, rl) m = Some m' ->
    run_tmr OpStore pcl <|addrl;xl;ml|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (addrv,addrl))::(AData (xv,xl))::s) (pcv,pcl)) 
               Silent 
               (AState m' i s (pcv+1,rpcl))

| step_jump: forall m i s pcv pcl pcv' pcl' rl rpcl, 
    index_list_Z pcv i = Some Jump ->
    run_tmr OpJump pcl <|pcl'|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (pcv',pcl'))::s) (pcv,pcl)) 
               Silent
               (AState m i s (pcv',rpcl))
               
| step_branchnz_true: forall m i s pcv pcl offv al rl rpcl,
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    run_tmr OpBranchNZ pcl <|al|> = Some (rpcl,rl) ->
    step_rules (AState m i ((AData (0,al))::s) (pcv,pcl)) 
               Silent
               (AState m i s (pcv+1,rpcl))

| step_branchnz_false: forall m i s pcv pcl offv av al rl rpcl, 
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    run_tmr OpBranchNZ pcl <|al|> = Some (rpcl,rl) ->
    av <> 0 ->
    step_rules (AState m i ((AData (av,al))::s) (pcv,pcl)) 
               Silent
               (AState m i s (pcv+offv,rpcl))

| step_call: forall m i s pcv pcl pcv' pcl' rl rpcl args a r, 
    index_list_Z pcv i = Some (Call a r) -> 
    run_tmr OpCall pcl <|pcl'|> = Some (rpcl,rl) ->
    length args = a ->
    (forall a, In a args -> exists d, a = AData d) ->
    step_rules (AState m i ((AData (pcv',pcl'))::args++s) (pcv,pcl)) 
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
    step_rules (AState m i (AData (xv,xl)::s) (pcv,pcl)) 
               (E (EInt (xv,rl))) (AState m i s (pcv+1,rpcl)).

Definition quasi_abstract_machine := 
  {| state := AS ;
    event := Event ;
    step := step_rules ;
    init_data := list Instr * list (@Atom T) * nat * T;
    init_state := fun id => 
                    let '(p,d,n,def) := id in
                    {| amem := replicate (0%Z, def) n ;
                       aimem := p ;
                       astk := map (fun a => AData a) d;
                       apc := (0%Z, def) |}
  |}.

Lemma step_rules_instr : forall m i s pcv pcl s' e,
  step_rules (AState m i s (pcv,pcl)) e s' ->
  exists instr, 
    index_list_Z pcv i = Some instr.
Proof.
  intros.
  inv H ; eauto.
Qed.

End QAMachine.

(** A version of the previous machine specialized for rules given as
symbolic lattice expressions, as defined in [Rules.v] *)

Section IFCQuasiAbstractMachine.

Context {T : Type}
        {Latt : JoinSemiLattice T}.

(** Get the "rule" for a given operation. *)
Variable fetch_rule : forall opcode : OpCode, AllowModify (labelCount opcode).

Definition ifc_run_tmr (opcode: OpCode) (pclab: T) (vlabs:Vector.t T (labelCount opcode)) :  option (T * T) :=
  let r := (fetch_rule opcode) in
  apply_rule r pclab vlabs.

Definition ifc_quasi_abstract_machine :=
  quasi_abstract_machine ifc_run_tmr.

End IFCQuasiAbstractMachine.

(** An instantiation of the Quasi-abstract machine with a particular
    symbolic rule table corresponding to the Abstract machine. *)

Section TINIQuasiAbstractMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Definition fetch_rule (opcode:OpCode) : (AllowModify (labelCount opcode)) :=
  match opcode with
    | OpNoop => ≪ TRUE , LabPC , __ ≫
    | OpAdd => ≪ TRUE,  LabPC , JOIN Lab1 Lab2 ≫
    | OpSub => ≪ TRUE, LabPC, JOIN Lab1 Lab2 ≫
    | OpPush => ≪ TRUE, LabPC , BOT ≫
    | OpPop => ≪ TRUE, LabPC , BOT ≫
    | OpLoad => ≪ TRUE, LabPC, JOIN Lab1 Lab2 ≫
    | OpStore => ≪ LE (JOIN Lab1 LabPC) Lab3,  (* addr, new value, old value *)
                   LabPC , 
                  JOIN Lab1 (JOIN Lab2 LabPC) ≫
    | OpJump => ≪ TRUE, JOIN Lab1 LabPC , __ ≫
    | OpBranchNZ => ≪ TRUE, JOIN Lab1 LabPC , __ ≫
    | OpCall => ≪ TRUE , JOIN Lab1 LabPC , LabPC ≫
    | OpRet => ≪ TRUE, Lab1 , __ ≫
    | OpVRet => ≪ TRUE, Lab2 , JOIN Lab1 LabPC ≫ (* value, return addr *)
    | OpOutput => ≪ TRUE, LabPC , JOIN Lab1 LabPC ≫ (* output value *)
    end.

Definition tini_quasi_abstract_machine := ifc_quasi_abstract_machine fetch_rule.

Ltac step_tmr :=
  match goal with
    | [ H: ifc_run_tmr _ _ _ _ = _  |- _ ] => inv H
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

  unfold ifc_run_tmr, apply_rule  in H3. simpl in H3.
  unfold Vector.nth_order in H3. simpl in H3.
  set (assert1 := addrl \_/ l <: ml) in *.
  case_eq assert1; intros;
  (unfold assert1 in * );
  (rewrite H in *; simpl in * ) ; allinv.
  eauto.

  congruence.
  congruence.
Qed.


End TINIQuasiAbstractMachine.
