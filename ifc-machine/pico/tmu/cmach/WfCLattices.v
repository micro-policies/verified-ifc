Require Import ZArith.
Require Import List.
Import ListNotations. 
Require Import LibTactics. 

Require Import TMUInstr.
Require Import Lattices.
Require Import CLattices.
Require Import Concrete.
Require Import CodeGen.
Require Import CodeSpecs.

(* Lattice-dependent parameters *)
Class WfConcreteLattice (T: Type) (L : JoinSemiLattice T) (CL: ConcreteLattice T) :=
{ ZToLab_labToZ_id: forall l, l = ZToLab (labToZ l)
; genJoin_spec: forall l l' m0 s0,
   HT  genJoin
       (fun m s => m = m0 /\
                   s = CData (labToZ l, handlerLabel) ::
                       CData (labToZ l', handlerLabel) :: s0)
       (fun m s => m = m0 /\
                   s = CData (labToZ (join l l'), handlerLabel) :: s0)
  (* NC: we could discharge this by implementing [genFlows] in terms of
   [genJoin], and using the fact that [flows l l' = true <-> join l l' = l']. *)
; genFlows_spec: forall l l' m0 s0,
   HT  genFlows
       (fun m s => m = m0 /\
                   s = CData (labToZ l, handlerLabel) ::
                       CData (labToZ l', handlerLabel) :: s0)
       (fun m s => m = m0 /\
                   s = CData (boolToZ (flows l l'), handlerLabel) :: s0)
}.

Lemma labToZ_inj: forall {L J C} {W: WfConcreteLattice L J C} (l1 l2: L),
  labToZ l1 = labToZ l2 -> l1 = l2.
Proof.
  intros.
  rewrite (ZToLab_labToZ_id l1).
  rewrite (ZToLab_labToZ_id l2).
  apply f_equal; auto.
Qed.

Require Import LatticeHL. 
Local Open Scope Z_scope. 

Lemma ZToLab_labToZ_id' : forall l, l = ZToLab (labToZ l).
Proof.
  intros.
  destruct l; auto.
Qed.

Lemma genJoin_spec' : forall l l' m0 s0,
   HT  genJoin
       (fun m s => m = m0 /\
                   s = CData (labToZ l, handlerLabel) ::
                       CData (labToZ l', handlerLabel) :: s0)
       (fun m s => m = m0 /\
                   s = CData (labToZ (join l l'), handlerLabel) :: s0).
Proof.
  intros.
  unfold genJoin, TMUHL. 
  destruct l; eapply HT_strengthen_premise.
    eapply ifNZ_spec_Z with (v:=0); auto.
    apply nop_spec.
    simpl. instantiate (1:= L). (* weird *)  destruct l';  jauto.

    eapply ifNZ_spec_NZ with (v:=1).
    eapply HT_compose.
    eapply pop_spec.  
    eapply push_spec''. 
    omega.
    simpl; jauto.
Qed.

Lemma genFlows_spec': forall l l' m0 s0,
   HT  genFlows
       (fun m s => m = m0 /\
                   s = CData (labToZ l, handlerLabel) ::
                       CData (labToZ l', handlerLabel) :: s0)
       (fun m s => m = m0 /\
                   s = CData (boolToZ (flows l l'), handlerLabel) :: s0).
Proof.
  intros.
  unfold genFlows, TMUHL.
  destruct l; eapply HT_strengthen_premise.  
     eapply ifNZ_spec_Z with (v:= 0); auto. 
     simpl (L <: l'). 
     eapply HT_compose.
     eapply pop_spec. 
     eapply genTrue_spec; eauto. 
     simpl. instantiate (2:= match l' with | L => 0 | H => 1 end).  (* awkward *) 
     instantiate (1:= L). instantiate (1 := L). (* still weird *) destruct l'; jauto.

     eapply ifNZ_spec_NZ with (v:= 1); try congruence. 
     eapply nop_spec.
     simpl. instantiate (1:= L); destruct l'; jauto.
Qed.

Instance TMUHLwf : WfConcreteLattice Lab HL TMUHL :=
{ ZToLab_labToZ_id := ZToLab_labToZ_id'
; genJoin_spec := genJoin_spec'
; genFlows_spec := genFlows_spec'
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