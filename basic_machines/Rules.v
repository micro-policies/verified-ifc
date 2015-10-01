Require Import List.
Require Import Omega.
Require Import Utils.
Require Import Lattices.
Require Import Instr.
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Vectors.Vector. 
Set Implicit Arguments.

(** Definition of a DSL for rule expressions
    and its evaluation function. *)

Section Rules.

(** All of these definitions are parameterized by [n], the number of input labels
supplied for a rule.  This permits us to check statically that the rule
doesn't use an undefined label. *)

Context {T: Type}.
Context {Latt: JoinSemiLattice T}.

(** * Label expressions *)

(** Labels variables *)
Inductive LAB (n: nat) : Type :=
| lab1 : 1 <= n -> LAB n
| lab2 : 2 <= n -> LAB n
| lab3 : 3 <= n -> LAB n
| labpc : LAB n. 

(** Output label expressions: the Modify part *)
Inductive rule_expr (n: nat) : Type :=
| L_Bot: rule_expr n
| L_Var: LAB n -> rule_expr n
| L_Join: rule_expr n -> rule_expr n -> rule_expr n. 

(** Side conditions for rules: the Allow part *)
Inductive rule_cond (n : nat) : Type :=
| A_True: @rule_cond n
| A_LE:  rule_expr n -> rule_expr n -> @rule_cond n 
| A_And: @rule_cond n -> @rule_cond n -> @rule_cond n
| A_Or: @rule_cond n -> @rule_cond n -> @rule_cond n
.

(** * Rules *)    
Record AllowModify (n:nat) := almod  {
   allow  : rule_cond n;
   labResPC : rule_expr n;   (** The label of the result PC *)
   labRes : rule_expr n      (** The label of the result value (always present but sometimes ignored) *)
}.

(** * Rule evaluation *)

(** [eval_var] is a mapping from abstract label names to concrete label
values (a context). It is constructed from the vector of input labels. *) 

Definition mk_eval_var {n:nat} (vs:Vector.t T n) (pc:T) : LAB n -> T := 
fun lv => 
    match lv with 
     | lab1 p => nth_order vs p 
     | lab2 p => nth_order vs p
     | lab3 p => nth_order vs p
     | labpc => pc
    end.

Fixpoint eval_expr {n:nat} (eval_var:LAB n -> T) (e: rule_expr n) : T :=
match e with
  | L_Bot => bot
  | L_Var labv => eval_var labv
  | L_Join e1 e2 => join (eval_expr eval_var e1) (eval_expr eval_var e2)
end. 

Fixpoint eval_cond {n:nat} (eval_var:LAB n -> T) (c: rule_cond n) : bool :=
match c with 
  | A_True => true
  | A_And c1 c2 => andb (eval_cond eval_var c1) (eval_cond eval_var c2)
  | A_Or c1 c2 =>  orb (eval_cond eval_var c1) (eval_cond eval_var c2)
  | A_LE e1 e2 => flows (eval_expr eval_var e1) (eval_expr eval_var e2)
end.

(** [apply_rule] evaluates the allow-modify r to the given parameters.
    Returns the result PC label and result value label,
    or nothing when the Allow condition fails. *)

Definition apply_rule {n:nat} (r: AllowModify n) 
  (pclab:T) (vlabs: Vector.t T n) : option (T * T) :=
  let eval_var := mk_eval_var vlabs pclab in
  if eval_cond eval_var (allow r) then
    Some (eval_expr eval_var (labResPC r),
          eval_expr eval_var (labRes r))
  else None.

End Rules. 

(** * Cosmetic notations for writing and applying rules *)
Fixpoint nlem (n:nat) (m:nat) : n<=(n+m).
Proof.
refine
(match m with
| O => _ (le_n n)
| S m' => _ (le_S _ _ (nlem n m'))
end). 
intros; omega. 
intros; zify; omega. 
Qed.

Notation "'≪' c1 , lpc , e1 '≫'" := (almod c1 lpc e1) (at level 95, no associativity).
Notation "'≪' c1 , lpc , '__' '≫'" := (almod c1 lpc (L_Bot _)) (at level 95, no associativity).
Notation "'LabPC'" := (L_Var (labpc _)).
Notation "'Lab1'" := (L_Var (lab1 (nlem _ _))).
Notation "'Lab2'" := (L_Var (lab2 (nlem _ _))).
Notation "'Lab3'" := (L_Var (lab3 (nlem _ _))).
Notation "'BOT'" := (L_Bot _).
Notation "'JOIN'" := L_Join.
Notation "'TRUE'" := (A_True _).
Notation "'AND'" := A_And.
Notation "'OR'" := A_Or.
Notation "'LE'" := A_LE. 
Notation "<||>" := (Vector.nil _).
Notation " <| x ; .. ; y |> " := (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..).


