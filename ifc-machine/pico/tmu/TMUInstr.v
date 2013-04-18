Require Import Datatypes.
Require Import Lattices.
Require Import ZArith.

Definition Atom {Label: Type} := (Z * Label)%type.

Inductive Instr :=
  | Noop : Instr 
  | Add : Instr 
  | Sub : Instr
  | Push : Z  -> Instr 
  | Load : Instr 
  | Store : Instr 
  | Jump : Instr 
  | BranchNZ : Z -> Instr
  | Call : nat -> bool -> Instr 
    (* Call n b : call to a function with n arguments, the boolean
       indicates a value or void returning function DD: do we really
       need the boolean flag? 
     DD: YES WE NEED IT !! *) 
  | Ret: Instr 
  | VRet : Instr 
  | Halt : Instr .


(* Convenience datatype for packaging the operation-specific label parameters
to TMU rules.  (If we ever move to having operation groups, we should expect
one constructor per group.)
There is no oplabel for Halt, as there is no rule for Halt. *)

Inductive OpCode : Type :=
| OpNoop 
| OpAdd  
| OpSub  
| OpPush 
| OpLoad 
| OpStore
| OpJump 
| OpBranchNZ 
| OpCall
| OpRet 
| OpVRet
.