Require Import List.
Require Import Omega.
Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import Monad.
Require Import Coq.Unicode.Utf8. 
Local Open Scope monad_scope.
Set Implicit Arguments.

(** This file defines the notion of rule, [AllowModify], and the
    associated manipulation, hypotheses...  Defining the simplest
    language you would need to express simple rules: we need to model

    - when the rule applies: [allow : rule_scond]

    - the label of the result value: [labRes : option rule_expr]

      Optional because not all ops return results.

    - the label of the result PC: [labResPC : rule_expr]

*)

Section Rules.

Context {T: Type}.
Context {Latt: JoinSemiLattice T}.


(** * Label expressions *)

(** Labels variables *)
Inductive LAB:= lab1 | lab2 | lab3 | labpc.

(** Expressions *)
Inductive rule_expr :=
| Var: LAB -> rule_expr
| Join: rule_expr -> rule_expr -> rule_expr.

(** Side conditions for rules: the Allow part *)
Inductive rule_scond: Type :=
| TRUE: rule_scond 
| LE: rule_expr  -> rule_expr  -> rule_scond 
| AND: rule_scond -> rule_scond -> rule_scond
| OR: rule_scond -> rule_scond -> rule_scond.

(** * Rules *)    
(** The allow-modify part of a rule *)
Record AllowModify := almod  {
   allow  : rule_scond;
   labRes : option rule_expr; (* The label of the result value *)
   labResPC : rule_expr       (* The label of the result PC *)
}.

(** * Rule evaluation *)


(** * Rules Evaluation *)    

(* eval_var is a mapping from abstract label names to concrete label
values (a context).  The function [apply_rule] below uses this context
to evaluate the rule ([AllowModify]).  *)
Definition mk_eval_var (v1 v2 v3: option T) (pc: T) : LAB -> option T :=
  fun lv => 
    match lv with 
        | lab1 => v1
        | lab2 => v2
        | lab3 => v3
        | labpc => Some pc
    end.

Fixpoint eval_expr eval_var (e: rule_expr): option T :=
  match e with 
    | Var labv => eval_var labv
    | Join e1 e2 => 
      match (eval_expr eval_var e1), (eval_expr eval_var e2) with 
        | Some v1, Some v2 => Some (join v1 v2)
        | _, _ => None
      end
  end.

(** eval_cond : evaluates a side_condition with given values for the argument *)
Fixpoint eval_cond eval_var (c: rule_scond) :bool:=
  match c with 
    | TRUE => true
    | AND c1 c2 => andb (eval_cond eval_var c1) (eval_cond eval_var c2)
    | OR c1 c2 => orb (eval_cond eval_var c1) (eval_cond eval_var c2)
    | LE e1 e2 => 
      match (eval_expr eval_var e1), (eval_expr eval_var e2) with 
          | Some v1, Some v2 => flows v1 v2
          | _ , _ => false 
      (* DD**: might not be enough if we need to distinguish a condition
       violation from an ill-formed condition *)
      end 
  end.


(** apply_rule applies the allow-modify r to the given parameters.=
    Returns the (optional) result value label and result PC label,
    or nothing when the side condition fails. *)
Definition apply_rule (r: AllowModify) (op1lab op2lab op3lab: option T) (pclab:T) : option (option T * T) :=
  let eval_var := mk_eval_var op1lab op2lab op3lab pclab in
  match eval_cond eval_var (allow r) with
    | false => None
    | true => 
      match (eval_expr eval_var (labResPC r)) with 
        | None => None
        | Some rpc => 
          match (labRes r) with 
            | Some lres => Some ((eval_expr eval_var lres), rpc)
            | None => Some (None, rpc)
          (* here is the place where DD** can apply *)
          end
      end
  end.

(** APT: Moved to TMUArules, so that it can pick up the definition of fetch_rule
(also so that this file no longer depends on TMUAbstact.)
An alternative would be to pass in fetch_rule as a parameter.

(** run_tmr : (TMR for Tag Managment Rules) fetches the rule 
   for the given opcode and applies it.  *)
Fixpoint run_tmr (opcode: OpCode) (lab1 lab2 lab3: option T) (pc: T):  @AMach T (option T * T) :=  
  let r := fetch_rule opcode in
  match apply_rule r lab1 lab2 lab3 pc with
    | None => error_
    | Some rv => ret rv
  end.
*)


End Rules.

(** * Cosmetic notations for writing rules *)
Notation "'≪' c1 , e1 , lpc '≫'" := (almod c1 (Some e1) lpc) (at level 95, no associativity).
Notation "'≪' c1 , '__' , lpc '≫'" := (almod c1 None lpc) (at level 95, no associativity).
Notation "'LabPC'" := (Var labpc).
Notation "'Lab1'" := (Var lab1).
Notation "'Lab2'" := (Var lab2).
Notation "'Lab3'" := (Var lab3).


(* OLD VERSION OF FETCH_RULE. KEEP IT FOR THE RECORD. *)
(*Definition fetch_rule (opCode:OpCode) : (AllowModify * (LAB -> option T)):=
  match oplab with
    | OpLabelNoop pc => (≪ TRUE , __ , LabPC ≫ , 
                          fun var => match var with
                                       | labpc => Some pc
                                       | _ => None
                                     end)
    | OpLabelAdd op1 op2 pc => (≪ TRUE, Join Lab1 Lab2 , LabPC ≫,
                                fun var =>  match var with 
                                              | lab1 => Some op1
                                              | lab2 => Some op2
                                              | labpc => Some pc 
                                              | _ => None
                                            end)
    | OpLabelSub op1 op2 pc => (≪ TRUE, Join Lab1 Lab2 , LabPC ≫,
                                fun var =>  match var with 
                                              | lab1 => Some op1
                                              | lab2 => Some op2
                                              | labpc => Some pc 
                                              | _ => None
                                            end)
    | OpLabelPush op pc => (≪ TRUE, Lab1 , LabPC ≫,
                            fun var => match var with 
                                         | lab1 => Some op
                                         | labpc => Some pc 
                                         | _ => None
                                       end)
    | OpLabelLoad loc data pc => (≪ TRUE, Join Lab1 Lab2, LabPC ≫,
                                  fun var => match var with
                                               | lab1 => Some loc
                                               | lab2 => Some data
                                               | labpc => Some pc 
                                               | _ => None
                                             end)
    | OpLabelStore loc new_data old_data pc => (≪ LE (Join Lab1 LabPC) Lab3, 
                                                  Join Lab1 (Join Lab2 LabPC), 
                                                  LabPC ≫,
                                                fun var => match var with
                                                             | lab1 => Some loc
                                                             | lab2 => Some new_data
                                                             | lab3 => Some old_data
                                                             | labpc => Some pc
                                                           end)
    | OpLabelJump jmp pc => (≪ TRUE, __ , Join Lab1 LabPC ≫,
                             fun var => match var with 
                                          | lab1 => Some jmp
                                          | labpc => Some pc
                                          | _ => None
                                        end)
    | OpLabelBranchNZ op pc => (≪ TRUE, __ , Join Lab1 LabPC ≫,
                                fun var => match var with 
                                             | lab1 => Some op
                                             | labpc => Some pc
                                             | _ => None
                                           end)
    | OpLabelCall call pc => (≪ TRUE ,LabPC ,Join Lab1 LabPC ≫,
                              fun var => match var with 
                                           | lab1 => Some call
                                           | labpc => Some pc 
                                           | _ => None
                                         end)
    | OpLabelRet pcl pc => (≪ TRUE, __ , Lab1 ≫,
                            fun var => match var with 
                                         | lab1 => Some pcl
                                         | labpc => Some pc 
                                         | _ => None
                                       end)
    | OpLabelVRet data pcl pc => (≪ TRUE, Join Lab1 LabPC, Lab2 ≫,
                                  fun var => match var with 
                                               | lab1 => Some data 
                                               | lab2 => Some pcl 
                                               | labpc => Some pc 
                                               | _ => None
                                             end)
    end.
*)