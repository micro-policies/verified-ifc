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

(* Relate an abstract fault description to initial handler memory. *)
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
  forall opcode op1l op2l op3l pcl m retaddr r_stack r_imem,

    let am := fetch_rule_impl opcode in
    let handler := faultHandler fetch_rule_impl in
    cache_hit m (mvector opcode op1l op2l op3l pcl) ->
    forall m' imem st pc priv,
      runsToEscape cstep 
                   0 (Z_of_nat (length handler)) 
                   (CState m (handler++r_imem) (CRet retaddr false false::r_stack) (0,handlerLabel) true)
                   (CState m' imem st pc priv) -> 
      match apply_rule am op1l op2l op3l pcl with
        | Some (olr,lpc) => handler_final_mem_matches' olr lpc m m' priv 
                     /\ pc = retaddr
                     /\ st = r_stack
        | None => m' = m /\ pc = (-1,handlerLabel) 
    end.


Section HandlerCorrect.
(* DD: Hopefully easier to parse *)

Variable get_rule : OpCode -> AllowModify.
Definition handler : list (@Instr T) := faultHandler get_rule.
Definition runHandler : @CS T -> @CS T -> Prop := runsToEscape cstep 0 (Z_of_nat (length handler)).
               
Conjecture handler_correct_succeed : 
  forall opcode op1l op2l op3l pcl m raddr s i i' olr lpc m' st pc priv,
  forall (INPUT: cache_hit m (mvector opcode op1l op2l op3l pcl))
         (RUNSH: runHandler (CState m (handler++i) (CRet raddr false false::s) (0,handlerLabel) true)
                            (CState m' i' st pc priv))
         (RULES: apply_rule (get_rule opcode) op1l op2l op3l pcl = Some (olr,lpc)),
    handler_final_mem_matches' olr lpc m m' priv 
    /\ pc = raddr 
    /\ st = s.
              
Conjecture handler_correct_fail : 
  forall opcode op1l op2l op3l pcl m raddr s i i' m' st pc priv,
  forall (INPUT: cache_hit m (mvector opcode op1l op2l op3l pcl))
         (RUNSH: runHandler (CState m (handler++i) (CRet raddr false false::s) (0,handlerLabel) true)
                            (CState m' i' st pc priv))
         (RULES: apply_rule (get_rule opcode) op1l op2l op3l pcl = None),
    m' = m /\ pc = (-1,handlerLabel).

(* We should also have the following: 
    - the handler code terminates
    - it does not modifies the user program
   But all these is probably much more easier to state and prove when get_rule is instanciated
*)

End HandlerCorrect.

End TMU.

