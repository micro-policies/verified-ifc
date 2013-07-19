Require Import ZArith.
Require Import List.
Import ListNotations. 
Require Import LibTactics. 

Require Import Instr Memory.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import CodeSpecs.

Local Open Scope Z_scope. 

Section fix_cblock.

Variable cblock : block privilege.
Variable stamp_cblock : Mem.stamp cblock = Kernel.

(* Lattice-dependent parameters *)
Class ConcreteLattice (T: Type) :=
{ labToZ :  T -> Z
; ZToLab :  Z -> T
; genBot : list Instr
; genJoin : list Instr 
; genFlows : list Instr
}.

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

Class WfConcreteLattice (T: Type) (L : JoinSemiLattice T) (CL: ConcreteLattice T) :=
{ ZToLab_labToZ_id: forall l, l = ZToLab (labToZ l)
; genBot_spec: forall m0 s0,
   HT cblock genBot
       (fun m s => m = m0 /\ s = s0)
       (fun m s => m = m0 /\ s = CData (Vint (labToZ bot), handlerTag) :: s0)
; genJoin_spec: forall l l' m0 s0,
   HT cblock genJoin
       (fun m s => m = m0 /\
                   s = CData (Vint (labToZ l), handlerTag) ::
                       CData (Vint (labToZ l'), handlerTag) :: s0)
       (fun m s => m = m0 /\
                   s = CData (Vint (labToZ (join l l')), handlerTag) :: s0)
  (* NC: we could discharge this by implementing [genFlows] in terms of
   [genJoin], and using the fact that [flows l l' = true <-> join l l' = l']. *)
; genFlows_spec: forall l l' m0 s0,
   HT cblock genFlows
       (fun m s => m = m0 /\
                   s = CData (Vint (labToZ l), handlerTag) ::
                       CData (Vint (labToZ l'), handlerTag) :: s0)
       (fun m s => m = m0 /\
                   s = CData (Vint (boolToZ (flows l l')), handlerTag) :: s0)
}.

Lemma labToZ_inj: forall {L J C} {W: WfConcreteLattice L J C} (l1 l2: L),
  labToZ l1 = labToZ l2 -> l1 = l2.
Proof.
  intros.
  rewrite (ZToLab_labToZ_id l1).
  rewrite (ZToLab_labToZ_id l2).
  apply f_equal; auto.
Qed.

Lemma ZToLab_labToZ_id' : forall l, l = ZToLab (labToZ l).
Proof.
  intros.
  destruct l; auto.
Qed.

Lemma genBot_spec' : forall m0 s0,
   HT cblock genBot
       (fun m s => m = m0 /\ s = s0)
       (fun m s => m = m0 /\ s = CData (Vint (labToZ bot), handlerTag) :: s0).
Proof.
   intros.
   unfold genBot, TMUHL. 
   eapply genFalse_spec; simpl; eauto.
Qed.

Lemma genJoin_spec' : forall l l' m0 s0,
   HT cblock genJoin
       (fun m s => m = m0 /\
                   s = CData (Vint (labToZ l), handlerTag) ::
                       CData (Vint (labToZ l'), handlerTag) :: s0)
       (fun m s => m = m0 /\
                   s = CData (Vint (labToZ (join l l')), handlerTag) :: s0).
Proof.
  intros.
  unfold genJoin, TMUHL. 
  cases l; cases l'; unfold labToZ in *;
    eapply HT_weaken_conclusion;
    try (eapply genOr_spec); simpl; eauto.
Qed.

Lemma genFlows_spec': forall l l' m0 s0,
   HT  cblock genFlows
       (fun m s => m = m0 /\
                   s = CData (Vint (labToZ l), handlerTag) ::
                       CData (Vint (labToZ l'), handlerTag) :: s0)
       (fun m s => m = m0 /\
                   s = CData (Vint (boolToZ (flows l l')), handlerTag) :: s0).
Proof.
  intros.
  unfold genFlows, TMUHL.
  cases l; cases l'; unfold labToZ in *;
    eapply HT_weaken_conclusion;
    try (eapply genImpl_spec); simpl; eauto.
Qed.

Instance TMUHLwf : WfConcreteLattice Lab HL TMUHL :=
{ ZToLab_labToZ_id := ZToLab_labToZ_id'
; genBot_spec := genBot_spec'
; genJoin_spec := genJoin_spec'
; genFlows_spec := genFlows_spec'
}.

End fix_cblock.
