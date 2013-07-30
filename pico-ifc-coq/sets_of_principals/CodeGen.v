
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

Definition storeAt loc :=
  push loc ++ [Store].

Definition loadFrom loc: code :=
  push loc ++ [Load].

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

(* Operations on booleans.  Not all of these are currently used. *)
(* Encoding of booleans: 0 = False, <> 0 = True *)

Definition boolToZ (b: bool): Z  := if b then 1 else 0.

Definition genFalse :=
  push (boolToZ false).

Definition genTrue :=
  push (boolToZ true).

Definition genAnd :=
  ifNZ nop (pop ++ genFalse).

Definition genOr :=
  ifNZ (pop ++ genTrue) nop.

Definition genNot :=
  ifNZ genFalse genTrue.

Definition genImpl :=
  (* [a -> b \equiv ~a \/ b] *)
  genNot ++ genOr.

Definition some c: code := c ++ push 1.
Definition none:   code := push 0.

(* Definition sub: code := [Sub]. *)

Definition genEq := [Sub] ++ genNot.

Definition genTestEqual (c1 c2: code): code :=
  c1 ++
  c2 ++
  genEq.

Definition dup := [Dup 0].

Definition swap := [Swap 1]. 

(* do c as along as top of stack is non-zero *)
Definition loopNZ (c : code) : code :=
  c ++ dup ++ (BranchNZ (- (Z_of_nat (length (c ++ dup)))) :: nil).

(* do c until (top of stack = 0) *)
Definition genRepeat (c:code) :=
 dup ++ ifNZ (loopNZ (c ++ push (-1) ++ [Add])) nop.


End CodeGeneration. 
