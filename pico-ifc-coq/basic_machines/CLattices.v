(* A [ConcreteLattice] is a way of encoding some abstract lattice, as
defined in [Lattices.v], in terms of integers. This is used in the
fault handler of the concrete machine to interpret the plain integer
tags as ifc-labels.

The encoding comprises two conversion functions, [labToZ] and
[ZToLab], and the implementation of three lattice primitives in
machine code, [genBot], [genJoin] and [genFlows]. We also define the
notion of a correct lattice encoding, [WfConcreteLattice], which will
be needed when proving the correctness of the fault handler.*)

Require Import ZArith.
Require Import List.
Import ListNotations. 
Require Import LibTactics. 

Require Import Instr.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import CodeTriples. 
Require Import CodeSpecs.

Local Open Scope Z_scope. 

(* A [ConcreteLattice] specifies how to encode some type [T] in terms
of integers. The last three methods, [genBot], [genJoin], and
[genFlows], are pieces of code that should implement the three lattice
methods [bot], [join] and [flows], operating on integers encoding
elements of [T]. Notice that we don't place any correctness
assumptions on these operations; these requirements are laid out in
the [WfConcreteLattice] class, given later. *)

Class ConcreteLattice (T: Type) :=
{ labToZ :  T -> Z
; ZToLab :  Z -> T
; genBot : list Instr
; genJoin : list Instr 
; genFlows : list Instr
}.

(* As an example of a lattice encoding, we can encode the simple
two-point lattice [Lab] by mapping 0 to [L] and any other integer to
[H]. Thus, [Lab] is encoded in integers just like the [bool] type. The
operations are simple boolean operations as defined in [CodeGen.v]. *)

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

(* We now define what it means for a lattice encoding to be
correct. The first requirement, [ZToLab_labToZ_id], says that decoding
an encoded label gives back the original label. The other three are
Hoare triples (as defined in [CodeSpecs.v]) specifying that each piece
of code in [ConcreteLattice] computes exactly what we expect. *)

Class WfConcreteLattice (T: Type) (L : JoinSemiLattice T) (CL: ConcreteLattice T) :=
{ ZToLab_labToZ_id: forall l, l = ZToLab (labToZ l)
; genBot_spec: forall Q,
   HT genBot
      (fun m s => Q m ((labToZ bot,handlerTag):::s))
      Q
; genJoin_spec: forall Q,
   HT  genJoin
       (fun m s => exists l l' s0, s = (labToZ l, handlerTag) :::
                                       (labToZ l', handlerTag)::: s0 /\
                                   Q m ((labToZ (join l l'), handlerTag) ::: s0))
       Q
  (* NC: we could discharge this by implementing [genFlows] in terms of
   [genJoin], and using the fact that [flows l l' = true <-> join l l' = l']. *)
; genFlows_spec: forall Q,
   HT  genFlows
       (fun m s => exists l l' s0, s = (labToZ l, handlerTag) :::
                                       (labToZ l', handlerTag)::: s0 /\
                            Q m ((boolToZ (flows l l'), handlerTag) ::: s0))
       Q
       
}.

Lemma labToZ_inj: forall {L J C} {W: WfConcreteLattice L J C} (l1 l2: L),
  labToZ l1 = labToZ l2 -> l1 = l2.
Proof.
  intros.
  rewrite (ZToLab_labToZ_id l1).
  rewrite (ZToLab_labToZ_id l2).
  apply f_equal; auto.
Qed.

(* We can easily show that the encoding of [Lab] above is correct. We
prove the four required lemmas, and them package them in the [TMUHLwf]
class below. *)

Lemma ZToLab_labToZ_id_HL : forall l, l = ZToLab (labToZ l).
Proof.
  intros.
  destruct l; auto.
Qed.

Lemma genBot_spec_HL : forall Q,
   HT genBot
      (fun m s => Q m ((labToZ bot,handlerTag):::s))
      Q.
Proof.
   intros.
   unfold genBot, TMUHL. 
   eapply genFalse_spec_wp; simpl; eauto.
Qed.

Lemma genJoin_spec_HL : forall Q,
   HT  genJoin
       (fun m s => exists l l' s0, s = (labToZ l, handlerTag) :::
                                       (labToZ l', handlerTag)::: s0 /\
                                   Q m ((labToZ (join l l'), handlerTag) ::: s0))
       Q.
Proof.
  intros.
  unfold genJoin, TMUHL.
  eapply HT_strengthen_premise.
  eapply genOr_spec_wp; eauto.
  simpl. intros. destruct H as [l [l' [s0 Hint]]]. intuition.
  cases l; cases l'; substs; unfold labToZ, boolToZ in *.
  exists false; exists false; exists s0 ; 
  intuition; eauto.
  exists false; exists true; exists s0 ; 
  intuition; eauto.
  exists true; exists false; exists s0 ; 
  intuition; eauto.
  exists true; exists true; exists s0 ; 
  intuition; eauto.
Qed.

Lemma genFlows_spec_HL: forall Q,
   HT  genFlows
       (fun m s => exists l l' s0, s = (labToZ l, handlerTag) :::
                                       (labToZ l', handlerTag)::: s0 /\
                            Q m ((boolToZ (flows l l'), handlerTag) ::: s0))
       Q.
Proof.
  intros.
  unfold genFlows, TMUHL, genImpl.
  eapply HT_compose_bwd. 
  eapply genOr_spec_wp.
  unfold genNot.
  eapply HT_strengthen_premise.
  eapply ifNZ_spec_existential.
  eapply push_spec_wp.
  eapply push_spec_wp.
  split_vc.
  destruct x, x0 ; simpl in *; intuition; substs; unfold boolToZ.
  exists true; exists false; exists x1 ; 
  intuition; eauto.
  exists true; exists true; exists x1 ; 
  intuition; eauto.
  exists false; exists false; exists x1 ; 
  intuition; eauto.
  exists false; exists true; exists x1 ; 
  intuition; eauto.
Qed.

Instance TMUHLwf : WfConcreteLattice Lab HL TMUHL :=
{ ZToLab_labToZ_id := ZToLab_labToZ_id_HL
; genBot_spec := genBot_spec_HL
; genJoin_spec := genJoin_spec_HL
; genFlows_spec := genFlows_spec_HL
}.
