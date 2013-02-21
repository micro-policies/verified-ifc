(* TMU Fault Handler *)

Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations. (* list notations *)

Require Import TMUInstr.
Require Import Lattices.
Require Import TMUConcreteR.
Require Import TMURules.
Require Import TMUTypes.
Require Import TMUCodeSpecs.
Require Import TMUCodeGen.
Require Import TMUConcreteMachine.

Section TMU. 

Open Local Scope Z_scope.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}.

(* Now some definitions and conjectures relating abstract fault descriptions to
   execution of the code above.  *) 

(* --------------------------------- *)
(* Specification of the handler code *)

(* Relate an abstract fault description to initial handler memory. *)
Definition handler_initial_mem_matches 
           (opcode: OpCode)
           (op1lab: option T) (op2lab:option T) (op3lab:option T) (pclab: T) 
           (m: memory) : Prop := 
  index_list_Z addrOpLabel m = Some(opCodeToZ opcode,handlerLabel)
  /\ (match op1lab with
      | Some op1 => index_list_Z addrTag1 m = Some (labToZ op1,handlerLabel)
      |    None=> True
   end)  
  /\ (match op2lab with
      | Some op2 => index_list_Z addrTag2 m = Some (labToZ op2,handlerLabel)
      | None => True
      end)
  /\ (match op3lab with
      | Some op3 => index_list_Z addrTag3 m = Some (labToZ op3,handlerLabel)
      | None => True
      end)
  /\ index_list_Z addrTagPC m = Some (labToZ pclab,handlerLabel)
.

(* Relate abstact rv to final handler memory. *)
Definition handler_final_mem_matches (rv: (option T * T)) (m0: memory) (m: memory) : Prop :=
  let (olr,lpc) := rv in
  (match olr with
   | Some lr => index_list_Z addrTagRes m = Some(labToZ lr,handlerLabel)
   | None => index_list_Z addrTagRes m = index_list_Z addrTagRes m0
   end) 
  /\ index_list_Z addrTagResPC m = Some (labToZ lpc,handlerLabel)
  /\ forall i, i <> addrTagRes -> i<> addrTagResPC -> 
               index_list_Z i m = index_list_Z i m0
.

Conjecture handler_correct :
  (* See ./notes.org (discussion of need for uniform rule generation)
  for discussion of [fetch_rule] *)
  forall (fetch_rule_impl : OpCode -> AllowModify) opcode op1lab op2lab op3lab pclab m0 retaddr rest_of_stack rest_of_imem,
    let am := fetch_rule_impl opcode in
    handler_initial_mem_matches opcode op1lab op2lab op3lab pclab m0  ->
    let handler := faultHandler fetch_rule_impl in
    forall m1 imem1 st1 pc1 priv1,
      runsToEscape cstep
                   0 (Z_of_nat (length handler)) 
                   (CState m0
                           (handler++rest_of_imem)
                           (CRet retaddr false false::rest_of_stack)
                           (0,handlerLabel)
                           true)
                   (CState m1 imem1 st1 pc1 priv1) -> 
      match apply_rule am op1lab op2lab op3lab pclab with
        | Some rv => handler_final_mem_matches rv m0 m1 
                     /\ pc1 = retaddr
                     /\ priv1 = false
                     /\ st1 = rest_of_stack
        | None => m1 = m0 /\ pc1 = (-1,handlerLabel) 
    end.

End TMU.

(* Module TMUHL := TMU(HL).  *)
  
(* Next, see if we can put this together with Concrete machine to define
a machine-with-firmware. *)

