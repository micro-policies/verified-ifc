Require Import ZArith.
Require Import List.
Import ListNotations. 

Require Import TMUInstr.
Require Import Lattices.
Require Import CodeGen.

(* Lattice-dependent parameters *)
Class ConcreteLattice (T: Type) :=
{ labToZ :  T -> Z
; ZToLab :  Z -> T
; genBot : list Instr
; genJoin : list Instr 
; genFlows : list Instr
}.

Require Import LatticeHL. 
Local Open Scope Z_scope. 

Instance TMUHL : ConcreteLattice Lab :=
{
  labToZ l :=
    match l with
      | L => boolToZ false
      | H => boolToZ true
    end
 
  ;ZToLab z :=
    match z with
      | 0 => L
      | _ => H
    end

  ;genBot := genFalse

  ;genJoin := genOr

  ;genFlows := genImpl
}.



(*
Module HL : TMULattice.  
(* Here are possible instantiations of lattice-dependent parameters for HL Lattice *)

  Require Import LatticeHL. 

  Local Open Scope Z_scope. 

  Definition labToZ (l:Lab) : Z :=
    match l with
      | L => 0
      | H => 1
    end.
 
  Definition ZToLab (z:Z) : Lab :=
    match z with
      | 0 => L
      | _ => H
    end.

  Definition T := Lab. 
  Definition Latt := HL. 

  Definition handlerLabel := H. 

  Definition pop := (@BranchNZ T) 1. 
  Definition push v := Push (v,handlerLabel).
  Definition branch ofs := 
  [push 1;
   BranchNZ (if ofs >=? 0 then ofs else ofs - 1 )]. 

  Definition genJoin :=
    [BranchNZ 3] ++
    branch 3 ++  (* length 2 *)
    [pop;
     push 1].

  Definition genFlows := (* l2 is on top of stack, l1 underneath *)
    [BranchNZ 2;
     BranchNZ 4;
     push 1] ++
     branch 2 ++ (* length 2 *)
     [push 0].
End HL. 

Module TMUHL := TMU(HL). 
*)