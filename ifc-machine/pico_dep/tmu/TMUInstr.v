Require Import Datatypes.
Require Import Lattices.
Require Import ZArith.

Definition Atom {Label: Type} := (Z * Label)%type.

Inductive Instr {Label: Type}:=
  | Noop : Instr 
  | Add : Instr 
  | Sub : Instr
  | Push : @Atom Label  -> Instr 
  | Load : Instr 
  | Store : Instr 
  | Jump : Instr 
  | BranchNZ : Z -> Instr
  | Call : nat -> bool -> Instr 
    (* Call n b : call to a function with n arguments, the boolean
       indicates a value or void returning function DD: do we really
       need the boolean flag? *) 
  | Ret: Instr 
  | VRet : Instr 
  | Halt : Instr .


(* Convenience datatype for packaging the operation-specific label parameters
to TMU rules.  (If we ever move to having operation groups, we should expect
one constructor per group.)
There is no oplabel for Halt, as there is no rule for Halt. *)

Inductive OpCode : nat -> Type :=
| OpNoop : OpCode 0
| OpAdd  : OpCode 2
| OpSub  : OpCode 2
| OpPush : OpCode 1
| OpLoad : OpCode 2
| OpStore : OpCode 3
| OpJump : OpCode 1
| OpBranchNZ : OpCode 1
| OpCall : OpCode 1
| OpRet : OpCode 1
| OpVRet : OpCode 2
.



