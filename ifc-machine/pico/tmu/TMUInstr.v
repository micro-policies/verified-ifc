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
       indicates a value or void returning function.
       We need that flag to ensure return stack are the same height
       when returning from two high calling context.  *) 
  | Ret: Instr 
  | VRet : Instr 
  | Halt : Instr
  | Output : Instr.


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
| OpOutput.

Definition opcode_of_instr (i : Instr) : option OpCode :=
  match i with
    | Noop => Some OpNoop
    | Add => Some OpAdd
    | Sub => Some OpSub
    | Push _ => Some OpPush
    | Load => Some OpLoad
    | Store => Some OpStore
    | Jump => Some OpJump
    | BranchNZ _ => Some OpBranchNZ
    | Call _ _ => Some OpCall
    | Ret => Some OpRet
    | VRet => Some OpVRet
    | Halt => None
    | Output => Some OpOutput
  end.
