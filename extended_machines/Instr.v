Require Import Datatypes.
Require Import ZArith.

Definition ident := nat.

Inductive Instr :=
  | Noop : Instr 
  | Add : Instr 
  | Sub : Instr
  | Eq : Instr
  | Dup : nat -> Instr
  | Swap : nat -> Instr
  | Push : Z  -> Instr 
  | Pop : Instr
  | PushCachePtr : Instr (* only used in kernel mode to retrieve the cache pointer *)
  | Alloc : Instr 
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
  | SysCall (id:ident) : Instr
  | Halt : Instr
  | Output : Instr
  | Unpack : Instr
  | Pack : Instr
  | SizeOf : Instr
  | GetOff : Instr.


(* Convenience datatype for packaging the operation-specific label parameters
to TMU rules.  (If we ever move to having operation groups, we should expect
one constructor per group.)
There is no opcode for Halt, as there is no rule for Halt.

There isn't one for SysCall because the code doens't use the cache. *)

Inductive OpCode : Type :=
| OpNoop 
| OpAdd  
| OpSub
| OpEq
| OpDup
| OpSwap
| OpPush 
| OpPop
| OpAlloc
| OpLoad 
| OpStore
| OpJump 
| OpBranchNZ 
| OpCall
| OpRet 
| OpVRet
| OpOutput
| OpSizeOf
| OpGetOff.

Definition opcode_of_instr (i : Instr) : option OpCode :=
  match i with
    | Noop => Some OpNoop
    | Add => Some OpAdd
    | Sub => Some OpSub
    | Eq => Some OpEq
    | Dup _ => Some OpDup
    | Swap _ => Some OpSwap
    | Push _ => Some OpPush
    | Pop => Some OpPop
    | Alloc => Some OpAlloc
    | Load => Some OpLoad
    | Store => Some OpStore
    | Jump => Some OpJump
    | BranchNZ _ => Some OpBranchNZ
    | Call _ _ => Some OpCall
    | Ret => Some OpRet
    | VRet => Some OpVRet
    | PushCachePtr => None (* this instruction is only used in kernel mode *)
    | SysCall _ => None
    | Halt => None
    | Output => Some OpOutput
    | Unpack => None
    | Pack => None
    | SizeOf => Some OpSizeOf
    | GetOff => Some OpGetOff
  end.
