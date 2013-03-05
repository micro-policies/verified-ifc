Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations.

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
   (* DD: not sure we need that precision for the None case.  Any
      label could be there. The machine is not to use it anyway. *)
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
  forall (fetch_rule_impl : OpCode -> AllowModify),
  forall opcode op1l op2l op3l pcl m retaddr c imem fhdl s,
    let am := fetch_rule_impl opcode in
    let handler := faultHandler fetch_rule_impl in
    cache_hit m (mvector opcode op1l op2l op3l pcl) ->
    exists c' st pc priv, 
      runsToEscape cstep_p 
                   0 (Z_of_nat (length handler)) 
                   (CState c m fhdl imem (CRet retaddr false false::s) (0,handlerLabel) true)
                   (CState c' m fhdl imem st pc priv) /\ 
      match apply_rule am op1l op2l op3l pcl with
        | (true,Some (olr,lpc)) => handler_final_mem_matches' olr lpc c c' priv 
                     /\ pc = retaddr
                     /\ st = s
        | (true,None) => c' = c /\ pc = (-1,handlerLabel) 
        | (false,_) => True
    end.


Section HandlerCorrect.
(* DD: Hopefully easier to parse *)

Variable get_rule : OpCode -> AllowModify.
Definition handler : list (@Instr T) := faultHandler get_rule.
Definition runHandler : @CS T -> @CS T -> Prop := runsToEscape cstep_p 0 (Z_of_nat (length handler)).
               
Conjecture handler_correct_succeed : 
  forall opcode op1l op2l op3l pcl c m raddr s i olr lpc,
  forall (INPUT: cache_hit c (mvector opcode op1l op2l op3l pcl))
         (RULE: apply_rule (get_rule opcode) op1l op2l op3l pcl = (true, Some (olr,lpc))),
    exists c',
    runHandler (CState c m handler i (CRet raddr false false::s) (0,handlerLabel) true)
               (CState c' m handler i s raddr false) /\
    handler_final_mem_matches' olr lpc c c' false.
              
Conjecture handler_correct_fail : 
  forall opcode op1l op2l op3l pcl c m raddr s i,
  forall (INPUT: cache_hit c (mvector opcode op1l op2l op3l pcl))
         (RULE: apply_rule (get_rule opcode) op1l op2l op3l pcl = (true,None)),
    exists st,
    runHandler (CState c m handler i (CRet raddr false false::s) (0,handlerLabel) true)
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

