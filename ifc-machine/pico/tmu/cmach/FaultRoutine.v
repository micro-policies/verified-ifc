Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations.
Require Vector.

Require Import TMUInstr.
Require Import Lattices.
Require Import Concrete.
Require Import ConcreteMachine.
Require Import Rules.
Require Import CLattices.
Require Import CodeSpecs.
Require Import CodeGen.

(* Specification of the handler code *)
(* Some definitions and conjectures relating abstract fault descriptions to
   execution of the code generated.  *) 

Section TMU. 

Open Local Scope Z_scope.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}.

(* Relate abstact rv to final handler memory. *)
Definition handler_final_mem_matches (rv: (option T * T)) (m: @memory T) (m': memory) : Prop :=
  let (olr,lpc) := rv in
  (match olr with
   | Some lr => tag_in_mem m' addrTagRes (labToZ lr)
   | None => index_list_Z addrTagRes m' = index_list_Z addrTagRes m 
   (* DD: not sure we need that precision for the None case.  *)
   end) 
  /\ tag_in_mem m' addrTagResPC (labToZ lpc)
  /\ update_cache_spec_rvec m m'.

(* DD: yet another version *)
Definition handler_final_mem_matches' (olr: option T) (lpc: T) (m: @memory T) (m': @memory T) (p: bool): Prop :=
  (match olr with
     | Some lr => cache_hit_read m' p lr lpc
     | None => exists l, cache_hit_read m' p l lpc
   end) 
  /\ update_cache_spec_rvec m m'.

Conjecture handler_correct : 
  forall (fetch_rule_impl : (forall (opcode:OpCode), AllowModify (labelCount opcode))),
  forall  opcode vls pcl m retaddr c imem fhdl s,
    let am := fetch_rule_impl opcode in
    let handler := @faultHandler T fetch_rule_impl in (* DD: Strange. Never had to specify T before... *)
    let '(op1l,op2l,op3l) := glue vls in 
    cache_hit c (mvector opcode op1l op2l op3l pcl) ->
    exists c' st pc priv, 
      runsToEscape (CState c m fhdl imem (CRet retaddr false false::s) (0,handlerLabel) true)
                   (CState c' m fhdl imem st pc priv) /\ 
      match apply_rule am vls pcl with
        | Some (olr,lpc) => handler_final_mem_matches' olr lpc c c' priv 
                     /\ pc = retaddr
                     /\ st = s
        | None => c' = c /\ pc = (-1,handlerLabel) 
    end.

(* TODO for Nathan: relate [runsToEscape] to [runsToEnd].*)

Section HandlerCorrect.
(* DD: Hopefully easier to parse *)

Variable get_rule : forall (opcode:OpCode), AllowModify (labelCount opcode).
Definition handler : list (@Instr T) := faultHandler get_rule.
               
Conjecture handler_correct_succeed : 
  forall opcode (vls: Vector.t T (labelCount opcode)) pcl c m raddr s i olr lpc,
  let '(op1l,op2l,op3l) := glue vls in 
  forall (INPUT: cache_hit c (mvector opcode op1l op2l op3l pcl))
         (RULE: apply_rule (get_rule opcode) vls pcl = Some (olr,lpc)),
    exists c',
    runsToEscape (CState c m handler i (CRet raddr false false::s) (0,handlerLabel) true)
                 (CState c' m handler i s raddr false) /\
    handler_final_mem_matches' olr lpc c c' false.
              
Conjecture handler_correct_fail : 
  forall opcode (vls:Vector.t T (labelCount opcode)) pcl c m raddr s i,
  let '(op1l,op2l,op3l) := glue vls in 
  forall (INPUT: cache_hit c (mvector opcode op1l op2l op3l pcl))
         (RULE: apply_rule (get_rule opcode) vls pcl = None),
    exists st,
    runsToEscape (CState c m handler i (CRet raddr false false::s) (0,handlerLabel) true)
                 (CState c m handler i st (-1,handlerLabel) true).

(*  We also have the following: 
    - the handler code terminates DONE
    - it does not modifies the user program UPCOMING
    - it preserves the handler code itself UPCOMING
In fact, preservation of all code (user and handler) is actually a universal property of the machines,
and should really be built into their definition, i.e. imem should not be part of the state. 
*)

End HandlerCorrect.

End TMU.

