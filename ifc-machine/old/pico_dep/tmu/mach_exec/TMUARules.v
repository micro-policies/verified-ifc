Require Import List.
Require Import Omega.

Require Import Utils.
Require Import TMUInstr.
Require Import Monad.
Require Import Lattices.

Require Import TMUAbstract.
Require Import TMURules.
Local Open Scope monad_scope.

Set Implicit Arguments.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

(** Get the "rule" for a given operation. *)
Definition fetch_rule (opcode:OpCode) : AllowModify :=
  match opcode with
    | OpNoop => ≪ TRUE , __ , LabPC ≫ 
    | OpAdd => ≪ TRUE, Join Lab1 Lab2 , LabPC ≫
    | OpSub => ≪ TRUE, Join Lab1 Lab2 , LabPC ≫
    | OpPush => ≪ TRUE, Lab1 , LabPC ≫
    | OpLoad => ≪ TRUE, Join Lab1 Lab2, LabPC ≫
    | OpStore => ≪ LE (Join Lab1 LabPC) Lab3, 
                  Join Lab1 (Join Lab2 LabPC), 
                  LabPC ≫
    | OpJump => ≪ TRUE, __ , Join Lab1 LabPC ≫
    | OpBranchNZ => ≪ TRUE, __ , Join Lab1 LabPC ≫
    | OpCall => ≪ TRUE ,LabPC ,Join Lab1 LabPC ≫
    | OpRet => ≪ TRUE, __ , Lab1 ≫
    | OpVRet => ≪ TRUE, Join Lab1 LabPC, Lab2 ≫
    end.

(** run_tmr : (TMR for Tag Managment Rules) fetches the rule 
   for the given opcode and applies it.  *)
Fixpoint run_tmr (opcode: OpCode) (lab1 lab2 lab3: option T) (pc: T):  @AMach T (option T * T) :=  
  let r := fetch_rule opcode in
  match apply_rule r lab1 lab2 lab3 pc with
    | None => error_
    | Some rv => ret rv
  end.

(* Notation handling the case where we need to use the labRes field of the tmr *)
Notation "<| x , y |> <- c1 ; c2" := 
  (Bind _ c1 (fun v => match v with 
                         | (Some x, y) => c2 
                         | (None, y) => error_ end))
  (right associativity, at level 84) : monad_scope.


(* The rule-based abstract machine transition relation *)
Local Open Scope Z_scope.

Definition step_rules : AMach unit :=
  [pcv,pcl] <- get_apc  ;
  instr <- index_aimem pcv;
  match instr with
    | Noop =>   
      [_,rpcl] <- run_tmr OpNoop None None None pcl   ;
      set_apc (pcv + 1, rpcl)

    | Add => 
      [x1v,x1l] <- pop_astk_data;
      [x2v,x2l] <- pop_astk_data;
      <| rl, rpcl |> <- run_tmr OpAdd (Some x1l) (Some x2l) None pcl;
      push_astk (AData ((x1v + x2v), rl));;
      set_apc (pcv + 1, rpcl)

    | Sub => 
      [x1v,x1l] <- pop_astk_data;
      [x2v,x2l] <- pop_astk_data;
      <| rl, rpcl |> <- run_tmr OpSub (Some x1l) (Some x2l) None pcl;
      push_astk (AData ((x1v - x2v), rl));;
      set_apc (pcv + 1, rpcl)

    | Push (cv,cl) =>
      <| rl,rpcl |> <- run_tmr OpPush (Some cl) None None pcl;
      push_astk (AData (cv, rl));;
      set_apc (pcv + 1, rpcl)

    | Load => 
      [addrv,addrl] <- pop_astk_data;
      [xv,xl] <- index_amem addrv;
      <| rl,rpcl |> <- run_tmr OpLoad (Some addrl) (Some xl) None pcl;
      push_astk (AData (xv, rl));;
      set_apc (pcv + 1, rpcl)

    | Store => 
      [addrv,addrl] <- pop_astk_data;
      [xv,xl] <- pop_astk_data;
      [mv,ml] <- index_amem addrv;
      <| rl,rpcl |> <- run_tmr OpStore (Some addrl) (Some xl) (Some ml) pcl;
      update_amem addrv (xv, rl);;
      set_apc (pcv + 1, rpcl)
    
    | Jump => 
      [pcv',pcl'] <- pop_astk_data;
      [_,rpcl] <- run_tmr  OpJump (Some pcl') None None pcl;
      set_apc (pcv', rpcl)

    | BranchNZ offv => (* relative target *)
      [av,al] <- pop_astk_data;
      [_,rpcl] <- run_tmr OpBranchNZ (Some al) None None pcl;
      set_apc ((if negb (av =? 0) then (pcv+offv) else pcv+1), rpcl)

    | Call a r => 
      [pcv',pcl'] <- pop_astk_data;
      <| rl,rpcl |> <- run_tmr OpCall (Some pcl') None None pcl;
      args <- pop_args a;  
      push_astk (ARet ((pcv+1), rl) r);;
      push_args args;;
      set_apc (pcv', rpcl)

    | Ret =>
      stk <- get_astk ;  
      ret_type <- drop_data (length stk) ;
      match ret_type with 
        | ARet (pcv',pcl') false => 
          [_,rpcl] <- run_tmr OpRet (Some pcl') None None pcl;
          set_apc (pcv', rpcl) 
        | ARet _ _ | AData _ => error_
      end

    | VRet =>
      stk <- get_astk ;  
      ret_type <- drop_data (length stk) ;
      match ret_type with 
        | ARet (pcv',pcl') true => 
          res <- top stk ; 
          match res with
            | AData (resv, resl) => 
              <| rl, rpcl |> <- run_tmr OpVRet (Some resl) (Some pcl') None pcl;
              push_astk (AData (resv, rl));;
              set_apc (pcv', rpcl)
            | ARet _ _ => error_
          end
        | ARet _ _ | AData _ => error_
      end

    | Halt => 
      error_   (* we're going to distingush sucessful executions
                  by looking at what was the last instruction *)

  end.

Lemma success_runSTO_None : forall  s,
  success s ->
  runSTO step_rules s = None.
Proof.
  intros. break_success. destruct s. simpl in *.
  destruct apc. simpl in *.
  unfold runSTO; simpl. unfold step_rules. simpl.
  unfold index_aimem, get_aimem. simpl in *.
  rewrite <- Heqoinstr. reflexivity.
Qed.
    
Lemma step_rules_non_ret_label_pc: forall m i stk pc s s' instr l,
  step_rules (AState m i stk (pc, l)) = Some (s, tt) ->
  index_aimem pc (AState m i stk (pc, l)) = Some (s', instr) ->
  instr <> Ret ->
  instr <> VRet ->
  exists (l' : T) (pc' : Z), apc s = (pc', l') /\ l <: l' = true.
Proof.
  intros.
  step_in @step_rules.
  step_in @get_apc.
  step_in get.
  rewrite H0 in H3; allinv.
  fetch_instr.
  destruct v; repeat sto_break_succ idtac.
 
  (* Noop *)
  inv H0.
  exists l; exists (pc+1)%Z ; split ; step_set_apc; eauto.  
  (* Add *) 
  step_pop_astk_data. 
  step_pop_astk_data. 
  step_set_apc; eauto.
  (* Sub *)
  step_pop_astk_data. 
  step_pop_astk_data. 
  step_set_apc; eauto.
  (* Push *)
  step_push_astk.
  destruct a. step_set_apc; eauto.
  (* Load *)
  step_pop_astk_data. 
  case_on @index_amem.
  fetch_mem.
  step_set_apc; eauto.
  (* Store *)
  step_pop_astk_data. 
  step_pop_astk_data. 
  fetch_mem.
  unfold apply_rule in * ; simpl in *.
  
  set (assert1 := vl \_/ l <: t) in *.
  case_eq assert1; intros;
  (unfold assert1 in *);
  (rewrite H0 in *; simpl in *) ; allinv.

  case_on @update_amem.

  step_in @update_amem.
  step_in @get_amem.
  destruct update_list_Z; allinv.
  step_in get.
  step_in @set_amem.
  step_in get.
  step_in put.
  step_set_apc.
  eauto.
  (* Jump *)
  step_pop_astk_data. 
  step_set_apc. eauto.
  (* BranchNZ *)
  step_pop_astk_data. 
  step_set_apc. destruct negb ; eauto with lat.

  (* Call *)
  step_pop_astk_data.  
  case_on @pop_args. 
  case_on @push_args. 
  exploit pop_args_spec ; eauto. intuition. 
  destruct H5 as [stk' [Hrev Ha]]. inv Ha. clear Heq.
  unfold upd_astk in *. simpl in *.
  exploit push_args_spec ; eauto.
  intuition. rewrite H3 in H.
  step_set_apc. 
  eauto.
  destruct v0 ; eauto.
  (* Ret *) congruence.
  (* VRet *) congruence.
  (* VRet *) congruence.
  (* Halt *) inv H.
Qed.

End ARuleMachine.
