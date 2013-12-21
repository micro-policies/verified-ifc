Require Import Datatypes.
Require Import ZArith.

(** Instructions used by the machines. *)

(** An [Atom] is an integer plus some metadata, and forms the basic
data unit in our machines. In the abstract and symbolic rule machine,
this metadata field contains an element from some arbitrary
information-flow lattice. In the concrete machine, it contains just a
plain integer. *)

Definition Atom {Label: Type} := (Z * Label)%type.

(** [Instr] is the type of instructions used in all three of our
machines. Our machines are stack machines, thus most instructions
operate on the machine stack, with no need for arguments. *)

Inductive Instr :=
  | Noop : Instr 
  | Add : Instr 
  | Sub : Instr
  | Push : Z  -> Instr
  | Pop : Instr

  (* Memory operations *)
  | Load : Instr 
  | Store : Instr

  | Jump : Instr 
  | BranchNZ : Z -> Instr

  (* [Call n b] : call a function with n arguments; the boolean
  indicates a value or void returning function.  We need that flag to
  ensure two calls to high contexts have the same stack layout upon a
  return *)
  | Call : nat -> bool -> Instr

  (* [Ret] and [VRet] return from function calls. The latter returns a
  value, while the former doesn't. *)
  | Ret: Instr 
  | VRet : Instr 

  | Halt : Instr
  | Output : Instr.

(** [OpCode]s are used to index TMU rules.  
There is no [OpCode] for Halt, as there is no stepping rule for Halt.*)
(* (If we ever move to having common rules for multiple instructions
("operation groups"), we should expect one OpCode per group.) *)

Inductive OpCode : Type :=
| OpNoop 
| OpAdd  
| OpSub  
| OpPush
| OpPop
| OpLoad 
| OpStore
| OpJump 
| OpBranchNZ 
| OpCall
| OpRet 
| OpVRet
| OpOutput.

Lemma dec_eq_OpCode: forall (o o': OpCode),
  o = o' \/ o <> o'.
Proof.
  destruct o; destruct o'; solve [ left; reflexivity | right; congruence ].
Qed.

(** Opcodes corresponding to instructions *)
Definition opcode_of_instr (i : Instr) : option OpCode :=
  match i with
    | Noop => Some OpNoop
    | Add => Some OpAdd
    | Sub => Some OpSub
    | Push _ => Some OpPush
    | Pop => Some OpPop
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
