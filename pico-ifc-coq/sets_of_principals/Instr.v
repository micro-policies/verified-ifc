Require Import Datatypes.
Require Import ZArith.

Definition Atom {Label: Type} := (Z * Label)%type.

Definition ident := nat.

Inductive Instr :=
  | Noop : Instr 
  | Add : Instr 
  | Sub : Instr
  | Dup : nat -> Instr
  | Swap : nat -> Instr
  | Push : Z  -> Instr
  | Pop : Instr
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
  | Output : Instr
  | SysCall (id:ident) : Instr
  | Halt : Instr       (* no execution rules for this *)
  | Alloc : Instr      (* only privileged execution rules for these ... *)
  | Unpack : Instr
  | Pack : Instr
.

(* Convenience datatype for packaging the operation-specific label parameters
to TMU rules.  (If we ever move to having operation groups, we should expect
one constructor per group.)
There is no oplabel for Halt, as there is no rule for Halt. 
Similarly, there are no opcodes for the privileged-mode-only instructions. *)

Inductive OpCode : Type :=
| OpNoop 
| OpAdd  
| OpSub  
| OpDup
| OpSwap
| OpPush
| OpPop
| OpLoad 
| OpStore
| OpJump 
| OpBranchNZ 
| OpCall
| OpRet 
| OpVRet
| OpOutput
. (* No opcode for SysCall since it does not use the cache *)

Definition opcode_of_instr (i : Instr) : option OpCode :=
  match i with
    | Noop => Some OpNoop
    | Add => Some OpAdd
    | Sub => Some OpSub
    | Dup _ => Some OpDup
    | Swap _ => Some OpSwap
    | Push _ => Some OpPush
    | Pop => Some OpPop
    | Load => Some OpLoad
    | Store => Some OpStore
    | Jump => Some OpJump
    | BranchNZ _ => Some OpBranchNZ
    | Call _ _ => Some OpCall
    | Ret => Some OpRet
    | VRet => Some OpVRet
    | Output => Some OpOutput
    | SysCall _ => None
    | _ => None
  end.

Lemma dec_eq_OpCode: forall (o o': OpCode),
  o = o' \/ o <> o'.
Proof.
  destruct o; destruct o'; solve [ left; reflexivity | right; congruence ].
Qed.


Section system_calls.

  Record syscall_info {T} : Type := 
    {
      si_arity : nat;
      si_sem : list (@Atom T) -> option (@Atom T)
             (* input stack *)   (* output atom *); (* and nothing about the memory *)
      si_pc : Z; (* the code position where we put the kernel code for this syscall *)
      si_instrs : list Instr (* the kernel code for this syscall *)
    }.

  Definition syscall_table T := ident -> option (@syscall_info T).

End system_calls.

