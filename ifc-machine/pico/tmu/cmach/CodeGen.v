Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations. (* list notations *)

Require Import TMUInstr.
Require Import Lattices.
Require Import Concrete.
Require Import CLattices.
Require Import Rules.

Local Open Scope Z_scope. 
Set Implicit Arguments. 

Section TMUCodeGeneration.

Context 
  {T: Type}
  {CLatt: ConcreteLattice T}.

Definition code := list (@Instr T).

(* Utility operations *)
Definition pop: code := [(@BranchNZ T) 1].
Definition nop: code := [].
Definition push v := Push (v,handlerLabel).
Definition push' v: code := [push v].

(* For multi-instruction operations that include an offset
   parameter, we adjust the offset if negative. 
   Not sure this is the best way. *)
Definition branchIfLocNeq addr val ofs :=
  [push ofs;
   push addr; 
   Load;
   push val;
   Sub;
   BranchNZ (if ofs >=? 0 then ofs else ofs - 5) ].

Definition branch ofs := 
  [push 1;
   BranchNZ (if ofs >=? 0 then ofs else ofs - 1 )]. 

Definition storeAt loc :=
  push' loc ++ [Store].

Definition loadFrom loc: code :=
  push' loc ++ [Load].

(* ---------------------------------------------------------------- *)
(* Code generation with ease of proof in mind *)

(* Skip the next [n] instructions conditionally *)
Definition skipNZ (n : nat) : code :=
  (* Add 1 because [BranchNZ] counts from the *current* pc *)
  (* Notation for lists and monads is conflicting ... *)
  BranchNZ (Z_of_nat (S n)) :: nil.

(* Skip the next [n] instructions unconditionally *)
Definition skip (n : nat) : code :=
  (* Pointless append here makes it easier to apply [HT_compose] *)
  push' 1 ++ skipNZ n.

(* Building block for if statement [ite] *)
Definition ifNZ t f :=
  let f' := f ++ skip (length t)
  in skipNZ (length f')
     ++ f'
     ++ t.

(* If statement: [if c then t else f] *)
Definition ite (c t f : code) : code :=
  c ++ ifNZ t f.

(* Case statement:

   (* cbs = (c1,bs) :: (c2,b2) :: ... *)
   if c1 then b1 else
   if c2 then b2 else
   ...
   if cn then bn else default

*)
Fixpoint cases (cbs : list (code * code)) (default: code) : code :=
  (* This is a foldr ... *)
  match cbs with
  | nil           => default
  | (c,b) :: cbs' => ite c b (cases cbs' default)
  end.

(* Version of [cases] with branches generated uniformly from
   indices:

   - [genC] generates branch guards.
   - [genB] generates branch bodies.

*)
Definition indexed_cases {I} (cnil: code) (genC genB: I -> code) (indices: list I): code :=
  cases (map (fun i => (genC i, genB i)) indices) cnil.

(* Operations on booleans.  Not all of these are currently used. *)
(* Encoding of booleans: 0 = False, <> 0 = True *)

Definition boolToZ (b: bool): Z  := if b then 1 else 0.

Definition genFalse :=
  push' (boolToZ false).

Definition genTrue :=
  push' (boolToZ true).

Definition genAnd :=
  ifNZ nop (pop ++ genFalse).

Definition genOr :=
  ifNZ (pop ++ genTrue) nop.

Definition genNot :=
  ifNZ genFalse genTrue.

(* --------------------- TMU Fault Handler code ----------------------------------- *)

(* XXX: NC: this Fault Handler specific code may belong back in
TMUFaultRoutine.v, but it will be easier to have it all in one place
while working on it ... *)

(* Compilation of rules *)

Definition genError :=
  [push (-1); Jump].

Definition genVar {n:nat} (l:LAB n) :=
  match l with
  (* NC: We assume the operand labels are stored at these memory
     addresses when the fault handler runs. *)
  | lab1 _ => loadFrom addrTag1
  | lab2 _ => loadFrom addrTag2
  | lab3 _ => loadFrom addrTag3
  | labpc => loadFrom addrTagPC
  end.

Fixpoint genExpr {n:nat} (e: rule_expr n) :=
  match e with
  | L_Var l => genVar l
  (* NC: push the arguments in reverse order. *)
  | L_Join e1 e2 => genExpr e2 ++ genExpr e1 ++ genJoin
 end.

Fixpoint genScond {n:nat} (s: rule_scond n) : code :=
  match s with
  | A_True => genTrue
  | A_LE e1 e2 => genExpr e2 ++ genExpr e1 ++ genFlows
  | A_And s1 s2 => genScond s2 ++ genScond s1 ++ genAnd 
  | A_Or s1 s2 => genScond s2 ++ genScond s1 ++ genOr 
  end.

Definition some c: code := c ++ push' 1.
Definition none:   code := push' 0.

Definition genApplyRule {n:nat} (am:AllowModify n): code :=
  ite (genScond (allow am))
      ((genExpr (labResPC am)) ++
       some
         match (labRes am) with
         | Some lres => some (genExpr lres)
         | None      => none
         end
      )
      none.

Definition sub: code := [Sub].

Definition genTestEqual (c1 c2: code): code :=
  c1 ++
  c2 ++
  sub ++
  genNot.

Section FaultHandler.

Definition genCheckOp (op:OpCode): code :=
  genTestEqual (push' (opCodeToZ op)) (loadFrom addrOpLabel).

Definition fetch_rule_impl_type: Type := forall (opcode:OpCode),  {n:nat & AllowModify n}.
Variable fetch_rule_impl: fetch_rule_impl_type.
Definition opcodes := 
  [OpNoop; OpAdd; OpSub; OpPush; OpLoad; OpStore; OpJump; OpBranchNZ; OpCall; OpRet; OpVRet].
Definition genApplyRule' op := genApplyRule (projT2 (fetch_rule_impl op)).
(* Fault handler that puts results on stack. *)
Definition genFaultHandlerStack: code :=
  indexed_cases nop genCheckOp genApplyRule' opcodes.

(* Write fault handler results to memory. *)
Definition genFaultHandlerMem: code :=
  ifNZ (ifNZ (storeAt addrTagRes) nop ++
        storeAt addrTagResPC ++
        genTrue)
       genFalse.

Definition faultHandler: code :=
  genFaultHandlerStack ++
  genFaultHandlerMem ++
  ifNZ [Ret] genError.

(* NC: or

   ite (genFaultHandlerStack ++ genFaultHandlerMem)
        [Ret]
        genError.
*)

End FaultHandler.

(*
Definition genRule {n:nat} (am:AllowModify n) (opcode:Z) : code :=
  let (allow, labresopt, labrespc) := am in 
  let body := 
    genScond allow ++
    [BranchNZ (Z.of_nat(length(genError)) +1)] ++
    genError ++ 
    genExpr labrespc ++
    storeAt addrTagResPC ++ 
    match labresopt with 
    | Some labres =>
      genExpr labres ++
      storeAt addrTagRes
    | None => []
    end ++
    [Ret] in
  (* test if correct opcode; if not, jump to end to fall through *)    
  branchIfLocNeq addrOpLabel opcode (Z.of_nat (length body)) ++ body.


Definition faultHandler (fetch_rule_impl: forall (opcode:OpCode),  AllowModify (labelCount opcode)) : code :=
  let gen (opcode:OpCode) := genRule (fetch_rule_impl opcode) (opCodeToZ opcode) in
  gen OpNoop ++
  gen OpAdd ++ 
  gen OpSub ++
  gen OpPush ++
  gen OpLoad ++
  gen OpStore ++
  gen OpJump ++
  gen OpBranchNZ ++
  gen OpCall ++
  gen OpRet ++
  gen OpVRet ++
  genError.
*)


End TMUCodeGeneration. 
