Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.

Require Import TMUInstr.
Require Import Abstract.
Require Import Rules.
Require Import AbstractCommon.

Require Vector.

Set Implicit Arguments.

Definition labelCount (c:OpCode) : nat :=
match c with
| OpNoop => 0
| OpAdd  => 2
| OpSub  => 2
| OpPush => 0
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

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

(** * Rules of the abstract machine *)
(** Get the "rule" for a given operation. *)
Definition fetch_rule (opcode:OpCode) : (AllowModify (labelCount opcode)) :=
  match opcode with
    | OpNoop => ≪ TRUE , __ , LabPC ≫ 
    | OpAdd => ≪ TRUE, JOIN Lab1 Lab2 , LabPC ≫ 
    | OpSub => ≪ TRUE, JOIN Lab1 Lab2 , LabPC ≫
    | OpPush => ≪ TRUE, BOT, LabPC ≫
    | OpLoad => ≪ TRUE, JOIN Lab1 Lab2, LabPC ≫
    | OpStore => ≪ LE (JOIN Lab1 LabPC) Lab3,  (* addr, new value, old value *)
                  JOIN Lab1 (JOIN Lab2 LabPC), 
                  LabPC ≫
    | OpJump => ≪ TRUE, __ , JOIN Lab1 LabPC ≫
    | OpBranchNZ => ≪ TRUE, __ , JOIN Lab1 LabPC ≫
    | OpCall => ≪ TRUE ,LabPC ,JOIN Lab1 LabPC ≫
    | OpRet => ≪ TRUE, __ , Lab1 ≫
    | OpVRet => ≪ TRUE, JOIN Lab1 LabPC, Lab2 ≫ (* value, return addr *)
    | OpOuput => ≪ TRUE, JOIN Lab1 LabPC, LabPC ≫ (* output value *)
    end.

(** run_tmr (TMR for Tag Managment Rules): fetches the rule for the
   given opcode and applies it.  *)
(** DD: Shall we propagate the boolean return code of apply_rule for
    distinguishing the kind of errors of the machine ?
    - abort/die abruptly when eval_var is buggy
    - exception on an IFC violation *)

Definition run_tmr (opcode: OpCode) (labs:Vector.t T (labelCount opcode)) (pc: T):  option (option T * T) :=  
  let r := fetch_rule opcode in
  apply_rule r labs pc.
   
Inductive step_rules : @AS T -> option (@Event T) -> @AS T -> Prop := 
| step_nop : forall m i s pcv pcl rpcl rl,
    index_list_Z pcv i = Some Noop ->
    run_tmr OpNoop <||> pcl = Some (rl,rpcl) ->
    step_rules (AState m i s (pcv,pcl)) None (AState m i s (pcv+1,rpcl))

| step_add: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l, 
    index_list_Z pcv i = Some Add ->
    run_tmr OpAdd <|x1l;x2l|> pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl)) 
               None
               (AState m i ((AData (x1v+x2v,rl))::s) (pcv+1,rpcl))

| step_sub: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l, 
    index_list_Z pcv i = Some Sub ->
    run_tmr OpSub <|x1l;x2l|> pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl)) 
               None
               (AState m i ((AData (x1v-x2v,rl))::s) (pcv+1,rpcl))

| step_push: forall m i s pcv pcl rpcl rl cv,
    index_list_Z pcv i = Some (Push cv) ->
    run_tmr OpPush <||> pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i s (pcv,pcl)) 
               None
               (AState m i ((AData (cv,rl))::s) (pcv+1,rpcl))

| step_load: forall m i s pcv pcl addrv addrl xv xl rl rpcl, 
    index_list_Z pcv i = Some Load ->
    index_list_Z addrv m = Some (xv,xl) ->
    run_tmr OpLoad <|addrl;xl|> pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i ((AData (addrv,addrl))::s) (pcv,pcl)) 
               None
               (AState m i ((AData (xv, rl))::s) (pcv+1,rpcl))

| step_store: forall m i s pcv pcl addrv addrl xv xl mv ml rl rpcl m', 
    index_list_Z pcv i = Some Store ->
    index_list_Z addrv m = Some (mv,ml) ->
    update_list_Z addrv (xv, rl) m = Some m' ->
    run_tmr OpStore <|addrl;xl;ml|> pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i ((AData (addrv,addrl))::(AData (xv,xl))::s) (pcv,pcl)) 
               None 
               (AState m' i s (pcv+1,rpcl))

| step_jump: forall m i s pcv pcl pcv' pcl' rl rpcl, 
    index_list_Z pcv i = Some Jump ->
    run_tmr OpJump <|pcl'|> pcl = Some (rl,rpcl) ->
    step_rules (AState m i ((AData (pcv',pcl'))::s) (pcv,pcl)) 
               None
               (AState m i s (pcv',rpcl))
               
| step_branchnz_true: forall m i s pcv pcl offv al rl rpcl,
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    run_tmr OpBranchNZ <|al|> pcl = Some (rl,rpcl) ->
    step_rules (AState m i ((AData (0,al))::s) (pcv,pcl)) 
               None
               (AState m i s (pcv+1,rpcl))

| step_branchnz_false: forall m i s pcv pcl offv av al rl rpcl, 
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    run_tmr OpBranchNZ <|al|> pcl = Some (rl,rpcl) ->
    av <> 0 ->
    step_rules (AState m i ((AData (av,al))::s) (pcv,pcl)) 
               None
               (AState m i s (pcv+offv,rpcl))

| step_call: forall m i s pcv pcl pcv' pcl' rl rpcl args a r, 
    index_list_Z pcv i = Some (Call a r) -> 
    run_tmr OpCall <|pcl'|> pcl = Some (Some rl,rpcl) ->
    length args = a ->
    (forall a, In a args -> exists d, a = AData d) ->
    step_rules (AState m i ((AData (pcv',pcl'))::args++s) (pcv,pcl)) 
               None
               (AState m i (args++(ARet (pcv+1,rl) r)::s) (pcv',rpcl))

| step_ret: forall m i s pcv pcl pcv' pcl' rl rpcl s' , 
    index_list_Z pcv i = Some Ret -> 
    pop_to_return s ((ARet (pcv',pcl') false)::s') ->
    run_tmr OpRet <|pcl'|> pcl = Some (rl,rpcl) ->
    step_rules (AState m i s  (pcv,pcl)) None (AState m i s' (pcv',rpcl))

| step_vret: forall m i s pcv pcl pcv' pcl' rl rpcl resv resl s' , 
    index_list_Z pcv i = Some VRet -> 
    pop_to_return s ((ARet (pcv',pcl') true)::s') ->
    run_tmr OpVRet <|resl;pcl'|> pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i (AData (resv,resl)::s) (pcv,pcl)) 
               None (AState m i (AData (resv, rl)::s') (pcv',rpcl))

| step_output: forall m i s pcv pcl rl rpcl xv xl, 
    index_list_Z pcv i = Some Output -> 
    run_tmr OpOutput <|xl|> pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i (AData (xv,xl)::s) (pcv,pcl)) 
               (Some (EInt (xv,rl))) (AState m i s (pcv+1,rpcl)).

(* Halt does not step. We're going to distingush sucessful executions by looking at what
   was the last instruction *)


(* DD: please don't delete that.
(* Inductive astep : @AS T -> (trace (@AS T)) -> @AS T -> Prop :=  *)
(* | astep_intro: forall s1 s2,  *)
(*                  step_rules s1 s2 -> *)
(*                  astep s1 (s1::E0 _) s2. *)
  
(* Inductive initial_AS : @AS T -> Prop := *)
(* | iAS_intro: forall m i, *)
(*              forall (MEM_INIT: forall addr, index_list_Z addr m = Some (0, bot)), *)
(*                initial_AS (AState m i nil (0,bot)). *)

(* Definition AMach : semantics (@AS T) := {| *)
(*                                          state := (@AS T) ; *)
(*                                          step := astep ; *)
(*                                          initial_state := initial_AS ; *)
(*                                          final_state := success *)
(*                                        |}. *)
*)

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

Ltac step_tmr := 
  match goal with
    | [ H: run_tmr _ _ _ = _  |- _ ] => inv H
  end. 

Lemma step_rules_non_ret_label_pc: forall m i stk pc l s instr e,
  step_rules (AState m i stk (pc, l)) e s ->
  index_list_Z pc i = Some instr ->
  instr <> Ret ->
  instr <> VRet ->
  exists (l' : T) (pc' : Z), apc s = (pc', l') /\ l <: l' = true.
Proof.
  intros.
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

(* This equivalent set of step rules corresponds to the "abstract"
abstract machine, as opposed to the "quasi" abstract one defined
above. The difference is that the IFC is built into the rules instead
of being defined separately. *)

(* AAA: FIXME: Should we move this to a separate file? *)

Inductive step_rules' : @AS T -> option (@Event T) -> @AS T -> Prop := 
| step_nop' : forall m i s pcv pcl,
    index_list_Z pcv i = Some Noop ->
    step_rules' (AState m i s (pcv,pcl)) None (AState m i s (pcv+1,pcl))

| step_add': forall m i s pcv pcl x1v x1l x2v x2l, 
    index_list_Z pcv i = Some Add ->
    step_rules' (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl)) 
                None
                (AState m i ((AData (x1v+x2v,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_sub': forall m i s pcv pcl x1v x1l x2v x2l, 
    index_list_Z pcv i = Some Sub ->
    step_rules' (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl)) 
                None
                (AState m i ((AData (x1v-x2v,x1l \_/ x2l))::s) (pcv+1,pcl))

| step_push': forall m i s pcv pcl cv,
    index_list_Z pcv i = Some (Push cv) ->
    step_rules' (AState m i s (pcv,pcl)) 
                None
                (AState m i ((AData (cv,bot))::s) (pcv+1,pcl))

| step_load': forall m i s pcv pcl addrv addrl xv xl, 
    index_list_Z pcv i = Some Load ->
    index_list_Z addrv m = Some (xv,xl) ->
    step_rules' (AState m i ((AData (addrv,addrl))::s) (pcv,pcl)) 
                None
                (AState m i ((AData (xv,addrl \_/ xl)::s)) (pcv+1,pcl))

| step_store': forall m i s pcv pcl addrv addrl xv xl mv ml m', 
    index_list_Z pcv i = Some Store ->
    index_list_Z addrv m = Some (mv,ml) ->
    addrl \_/ pcl <: ml = true ->
    update_list_Z addrv (xv, addrl \_/ (xl \_/ pcl)) m = Some m' ->
    step_rules' (AState m i ((AData (addrv,addrl))::(AData (xv,xl))::s) (pcv,pcl)) 
                None 
                (AState m' i s (pcv+1,pcl))

| step_jump': forall m i s pcv pcl pcv' pcl',
    index_list_Z pcv i = Some Jump ->
    step_rules' (AState m i ((AData (pcv',pcl'))::s) (pcv,pcl)) 
                None
                (AState m i s (pcv',pcl' \_/ pcl))
               
| step_branchnz_true': forall m i s pcv pcl offv al,
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    step_rules' (AState m i ((AData (0,al))::s) (pcv,pcl)) 
                None
                (AState m i s (pcv+1,al \_/ pcl))

| step_branchnz_false': forall m i s pcv pcl offv av al, 
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    av <> 0 ->
    step_rules' (AState m i ((AData (av,al))::s) (pcv,pcl)) 
                None
                (AState m i s (pcv+offv,al \_/ pcl))

| step_call': forall m i s pcv pcl pcv' pcl' args a r, 
    index_list_Z pcv i = Some (Call a r) -> 
    length args = a ->
    (forall a, In a args -> exists d, a = AData d) ->
    step_rules' (AState m i ((AData (pcv',pcl'))::args++s) (pcv,pcl)) 
                None
                (AState m i (args++(ARet (pcv+1,pcl) r)::s) (pcv',pcl' \_/ pcl))

| step_ret': forall m i s pcv pcl pcv' pcl' s' , 
    index_list_Z pcv i = Some Ret -> 
    pop_to_return s ((ARet (pcv',pcl') false)::s') ->
    step_rules' (AState m i s (pcv,pcl)) None (AState m i s' (pcv',pcl'))

| step_vret': forall m i s pcv pcl pcv' pcl' resv resl s' , 
    index_list_Z pcv i = Some VRet -> 
    pop_to_return s ((ARet (pcv',pcl') true)::s') ->
    step_rules' (AState m i (AData (resv,resl)::s) (pcv,pcl)) 
                None (AState m i (AData (resv, resl \_/ pcl)::s') (pcv',pcl'))

| step_output': forall m i s pcv pcl xv xl, 
    index_list_Z pcv i = Some Output -> 
    step_rules' (AState m i (AData (xv,xl)::s) (pcv,pcl)) 
                (Some (EInt (xv,xl \_/ pcl))) (AState m i s (pcv+1,pcl)).

Lemma step_rules_equiv : forall s e s',
                           step_rules s e s' <-> step_rules' s e s'.
Proof.
  intros.
  split; intro H; inv H;
  unfold run_tmr, apply_rule in *;
  simpl in *;
  repeat match goal with
           | H : Some _ = Some _ |- _ =>
             inv H
           | H : (if ?b then _ else _) = _ |- _ =>
             destruct b eqn:E; inv H
         end;
  unfold Vector.nth_order in *; simpl in *;
  try econstructor (solve [compute; eauto]).

  econstructor; eauto.
  unfold run_tmr, apply_rule. simpl.
  unfold Vector.nth_order. simpl.
  rewrite H2. trivial.
Qed.

End ARuleMachine.
