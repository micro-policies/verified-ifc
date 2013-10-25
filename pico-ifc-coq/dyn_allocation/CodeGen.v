(** Generic support for writing (privileged) concrete machine programs. *)

Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations.

Require Import Instr.

Local Open Scope Z_scope.
Set Implicit Arguments.

Section CodeGeneration.

Definition code := list Instr.

(* Utility operations *)
(* now a real instruction: Definition pop: code := [BranchNZ 1]. *)
Definition pop : code := [Pop].  (* for backward compatibility. *)
(* still a real instruction (why?): Definition nop: code := []. *)
Definition nop := [Noop].
Definition push v: code := [Push v].
Definition push_cptr ofs: code := [PushCachePtr;Push ofs;Add].

Definition storeAt loc :=
  push_cptr loc ++ [Store].

Definition loadFromCache loc: code :=
  push_cptr loc ++ [Load].


(* ---------------------------------------------------------------- *)
(* Code generation with ease of proof in mind *)

(* Skip the next [n] instructions conditionally *)
Definition skipNZ (n : nat) : code :=
  (* Add 1 because [BranchNZ] counts from the *current* pc *)
  [BranchNZ (Z_of_nat (S n))].

(* Skip the next [n] instructions unconditionally *)
Definition skip (n : nat) : code :=
  (* Pointless append here makes it easier to apply [HT_compose] *)
  push 1 ++ skipNZ n.

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

Definition genEq := [Eq].

(* Operations on booleans.  Not all of these are currently used. *)
(* Encoding of booleans: Vint 0 = False, <> Vint 0 = True *)

Definition boolToZ (b: bool): Z  := if b then 1 else 0.

Definition genFalse :=
  push (boolToZ false).

Definition genTrue :=
  push (boolToZ true).

Definition genAnd :=
  push 0 ++ genEq ++ ifNZ (pop ++ genFalse) nop.

Definition genOr :=
  push 0 ++ genEq ++ ifNZ nop (pop ++ genTrue).

Definition genNot :=
  push 0 ++ genEq.

Definition genImpl :=
  (* [a -> b \equiv ~a \/ b] *)
  genNot ++ genOr.

Definition some c: code := c ++ push 1.
Definition none:   code := push 0.

Definition sub: code := [Sub].

Definition genTestEqual (c1 c2: code): code :=
  c1 ++
  c2 ++
  genEq.

Definition dup := [Dup 0].

Definition swap := [Swap 1].

(* do c as along as top of stack is non-zero *)
Definition genLoop (c : code) : code :=
  c ++ dup ++ (BranchNZ (- (Z_of_nat (length (c ++ dup)))) :: nil).

(* do c until (top of stack = 0) *)
Definition genFor (c:code) :=
 dup ++ ifNZ (genLoop (c ++ push (-1) ++ [Add])) nop.

Definition jump_back (c : code) :=
  c ++ push 1 ++ [BranchNZ (- Z.of_nat (length c + 1))].

Definition while_body (c b : code) :=
  c ++ genNot ++ skipNZ (length b + 2) ++ b.

Definition while (c b : code) : code :=
  jump_back (while_body c b).

Definition genError := push (-1) ++ [Jump].

(* Expects an option on the stack, as encoded by the [some] and [none]
generators. If the element is a [some], returns that
element. Otherwise, causes an error. *)

Definition genSysRet : code := ifNZ [Ret] genError.
Definition genSysVRet : code := ifNZ [VRet] genError.

End CodeGeneration.
