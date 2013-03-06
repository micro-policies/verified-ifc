Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.

Require Import TMUInstr.
Require Import Abstract.
Require Import Rules.

Set Implicit Arguments.
Local Open Scope Z_scope.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

(** * Rules of the abstract machine *)
(** Get the "rule" for a given operation. *)
Definition fetch_rule (opcode:OpCode) : AllowModify :=
  match opcode with
    | OpNoop => ≪ TRUE , __ , LabPC ≫ 
    | OpAdd => ≪ TRUE, Join Lab1 Lab2 , LabPC ≫
    | OpSub => ≪ TRUE, Join Lab1 Lab2 , LabPC ≫
    | OpPush => ≪ TRUE, Lab1 , LabPC ≫
    | OpLoad => ≪ TRUE, Join Lab1 Lab2, LabPC ≫
    | OpStore => ≪ LE (Join Lab1 LabPC) Lab3,  (* addr, new value, old value *)
                  Join Lab1 (Join Lab2 LabPC), 
                  LabPC ≫
    | OpJump => ≪ TRUE, __ , Join Lab1 LabPC ≫
    | OpBranchNZ => ≪ TRUE, __ , Join Lab1 LabPC ≫
    | OpCall => ≪ TRUE ,LabPC ,Join Lab1 LabPC ≫
    | OpRet => ≪ TRUE, __ , Lab1 ≫
    | OpVRet => ≪ TRUE, Join Lab1 LabPC, Lab2 ≫ (* value, return addr *)
    end.

(** run_tmr (TMR for Tag Managment Rules): fetches the rule for the
   given opcode and applies it.  *)
(** DD: Shall we propagate the boolean return code of apply_rule for
    distinguishing the kind of errors of the machine ?
    - abort/die abruptly when eval_var is buggy
    - exception on an IFC violation
 *)
Fixpoint run_tmr (opcode: OpCode) (lab1 lab2 lab3: option T) (pc: T):  option (option T * T) :=  
  let r := fetch_rule opcode in
  match apply_rule r lab1 lab2 lab3 pc with 
      | (true,res) => res
      | (false,_) => None
  end.

(** * Rule-based abstract machine transition relation *)
Inductive pop_to_return : list (@StkElmt T) -> list (@StkElmt T) -> Prop := 
| sptr_done: forall a b s,
    pop_to_return ((ARet a b)::s) ((ARet a b)::s)
| sptr_pop: forall a s s',
    pop_to_return s s' ->
    pop_to_return ((AData a)::s) s'.

Lemma pop_to_return_ret : forall s1 s2,
  pop_to_return s1 s2 ->
  exists a b s, s2 = (@ARet T a b)::s.
Proof.
  induction 1; intros; simpl; eauto.
Qed.  
  
Lemma pop_to_return_spec : forall s1 s2,
  pop_to_return s1 s2 ->
  exists dstk, exists stk a b,   
    s1 = dstk++(ARet a b)::stk
    /\ (forall e, In e dstk -> exists a, e = AData a).
Proof.
  induction 1; intros; simpl in *. 
  exists nil ; exists s ; exists a ; exists b.
  simpl ; split ; eauto.
  intuition.

  destruct IHpop_to_return as [dstk [stk [a0 [b0 [Hs Hdstk]]]]].
  subst.
  exists ((AData a)::dstk).
  exists stk ; eauto.
  exists a0 ; exists b0 ; split ; eauto.
  intros. inv H0.
  eauto.
  eapply Hdstk; auto.
 Qed.

Lemma pop_to_return_spec2: forall  s1 s2  b1 b2 a1 a2 dstk,
 pop_to_return (dstk ++ ARet a1 b1 :: s2)
               (ARet a2 b2 :: s1) ->
 (forall e : StkElmt, In e dstk -> exists a : @Atom T, e = AData a) ->
 ARet a1 b1 =  ARet a2 b2.
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *. 
  inv H. destruct (H0 (ARet a2 b2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

Lemma pop_to_return_spec3: forall s1 s2 b1 b2 a1 a2 dstk,
 pop_to_return (dstk ++ ARet a1 b1 :: s2)
               (ARet a2 b2 :: s1) ->
 (forall e, In e dstk -> exists a : @Atom T, e = AData a) ->
 s1 = s2 .
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *. 
  inv H. destruct (H0 (ARet a2 b2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.
   
Inductive step_rules : @AS T -> @AS T -> Prop := 
| step_nop : forall m i s pcv pcl rpcl rl,
    index_list_Z pcv i = Some Noop ->
    run_tmr OpNoop None None None pcl = Some (rl,rpcl) ->
    step_rules (AState m i s (pcv,pcl)) (AState m i s (pcv+1,rpcl))

| step_add: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l, 
    index_list_Z pcv i = Some Add ->
    run_tmr OpAdd (Some x1l) (Some x2l) None pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl)) 
               (AState m i ((AData (x1v+x2v,rl))::s) (pcv+1,rpcl))

| step_sub: forall m i s pcv pcl rpcl rl x1v x1l x2v x2l, 
    index_list_Z pcv i = Some Sub ->
    run_tmr OpSub (Some x1l) (Some x2l) None pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i ((AData (x1v,x1l)::(AData (x2v,x2l))::s)) (pcv,pcl)) 
               (AState m i ((AData (x1v-x2v,rl))::s) (pcv+1,rpcl))

| step_push: forall m i s pcv pcl rpcl rl cv cl,
    index_list_Z pcv i = Some (Push (cv,cl)) ->
    run_tmr OpPush (Some cl) None None pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i s (pcv,pcl)) 
               (AState m i ((AData (cv,rl))::s) (pcv+1,rpcl))

| step_load: forall m i s pcv pcl addrv addrl xv xl rl rpcl, 
    index_list_Z pcv i = Some Load ->
    index_list_Z addrv m = Some (xv,xl) ->
    run_tmr OpLoad (Some addrl) (Some xl) None pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i ((AData (addrv,addrl))::s) (pcv,pcl)) 
               (AState m i ((AData (xv, rl))::s) (pcv+1,rpcl))

| step_store: forall m i s pcv pcl addrv addrl xv xl mv ml rl rpcl m', 
    index_list_Z pcv i = Some Store ->
    index_list_Z addrv m = Some (mv,ml) ->
    update_list_Z addrv (xv, rl) m = Some m' ->
    run_tmr OpStore (Some addrl) (Some xl) (Some ml) pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i ((AData (addrv,addrl))::(AData (xv,xl))::s) (pcv,pcl)) 
               (AState m' i s (pcv+1,rpcl))

| step_jump: forall m i s pcv pcl pcv' pcl' rl rpcl, 
    index_list_Z pcv i = Some Jump ->
    run_tmr OpJump (Some pcl') None None pcl = Some (rl,rpcl) ->
    step_rules (AState m i ((AData (pcv',pcl'))::s) (pcv,pcl)) 
               (AState m i s (pcv',rpcl))
               
| step_branchnz_true: forall m i s pcv pcl offv al rl rpcl,
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    run_tmr OpBranchNZ (Some al) None None pcl = Some (rl,rpcl) ->
    step_rules (AState m i ((AData (0,al))::s) (pcv,pcl)) 
               (AState m i s (pcv+1,rpcl))

| step_branchnz_false: forall m i s pcv pcl offv av al rl rpcl, 
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    run_tmr OpBranchNZ (Some al) None None pcl = Some (rl,rpcl) ->
    av <> 0 ->
    step_rules (AState m i ((AData (av,al))::s) (pcv,pcl)) 
               (AState m i s (pcv+offv,rpcl))

| step_call: forall m i s pcv pcl pcv' pcl' rl rpcl args a r, 
    index_list_Z pcv i = Some (Call a r) -> 
    run_tmr OpCall (Some pcl') None None pcl = Some (Some rl,rpcl) ->
    length args = a ->
    (forall a, In a args -> exists d, a = AData d) ->
    step_rules (AState m i ((AData (pcv',pcl'))::args++s) (pcv,pcl)) 
               (AState m i (args++(ARet (pcv+1,rl) r)::s) (pcv',rpcl))

| step_ret: forall m i s pcv pcl pcv' pcl' rl rpcl s' , 
    index_list_Z pcv i = Some Ret -> 
    pop_to_return s ((ARet (pcv',pcl') false)::s') ->
    run_tmr OpRet (Some pcl') None None pcl = Some (rl,rpcl) ->
    step_rules (AState m i s  (pcv,pcl)) 
               (AState m i s' (pcv',rpcl))

| step_vret: forall m i s pcv pcl pcv' pcl' rl rpcl resv resl s' , 
    index_list_Z pcv i = Some VRet -> 
    pop_to_return s ((ARet (pcv',pcl') true)::s') ->
    run_tmr OpVRet (Some resl) (Some pcl') None pcl = Some (Some rl,rpcl) ->
    step_rules (AState m i (AData (resv,resl)::s) (pcv,pcl)) 
               (AState m i (AData (resv, rl)::s') (pcv',rpcl)).

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

Lemma step_rules_instr : forall m i s pcv pcl s',
  step_rules (AState m i s (pcv,pcl)) s' ->
  exists instr, 
    index_list_Z pcv i = Some instr.
Proof.
  intros.
  inv H ; eauto.
Qed.

Lemma success_runSTO_None : forall  s,
  success s ->  
  forall s', ~ step_rules s s'.
Proof.
  intros. intros HCont. break_success.
  inv HCont; simpl in * ; try congruence.
Qed.

Lemma spec_find_return : 
  forall (T : Type)  (stk : list (@StkElmt T)) a b s,
    find_return stk = Some (a, b, s) ->
    (exists stk' : list StkElmt,
       (forall e, In e stk' -> exists a, e = AData a) /\
       stk = stk' ++ ((ARet a b):: s)).
Proof.
  induction stk; intros.
  inv H.
  simpl in *. destruct a. 
  exploit IHstk; eauto. intros [stk' [Hdata Hstk]].
  rewrite Hstk. exists (AData a :: stk'). split ; auto.
  intros. inv H0 ; auto. eauto.
  inv H. 
  exists nil. split ; auto.
  intros. inv H.
Qed.

Ltac step_tmr := 
  match goal with
    | [ H: run_tmr _ _ _ _ _ = _  |- _ ] => inv H
  end. 

Lemma step_rules_non_ret_label_pc: forall m i stk pc l s instr,
  step_rules (AState m i stk (pc, l)) s ->
  index_list_Z pc i = Some instr ->
  instr <> Ret ->
  instr <> VRet ->
  exists (l' : T) (pc' : Z), apc s = (pc', l') /\ l <: l' = true.
Proof.
  intros.
  inv H; try step_tmr ; simpl in *; eauto.
  
  unfold apply_rule in * ; simpl in *.
  set (assert1 := addrl \_/ l <: ml) in *.
  case_eq assert1; intros;
  (unfold assert1 in *);
  (rewrite H in *; simpl in *) ; allinv.
  eauto.
  
  congruence.
  congruence.
Qed.

End ARuleMachine.
