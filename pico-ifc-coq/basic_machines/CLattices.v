(* A [ConcreteLattice] is a way of computing over the elements of some
encodable lattice, as defined in [Encodable.v] and [Lattices.v]. This
is used in the fault handler of the concrete machine to interpret the
plain integer tags as ifc-labels.

This comprises the implementation of three lattice primitives in
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
Require Import Encodable.

Local Open Scope Z_scope. 

(* The methods of [ConcreteLattice], are pieces of code that should
implement the three lattice methods [bot], [join] and [flows],
operating on integers encoding elements of [T]. Notice that we don't
place any correctness assumptions on these operations; these
requirements are laid out in the [WfConcreteLattice] class, given
later. *)

Class ConcreteLattice (T: Type) :=
{ genBot : list Instr
; genJoin : list Instr
; genFlows : list Instr
}.

(* As an example, we can implement the simple H/L lattice using the
implementation of the corresponding boolean operations defined in
[CodeGen.v] *)

Instance TMUHL : ConcreteLattice Lab :=
{
  genBot := genFalse
  ;genJoin := genOr
  ;genFlows := genImpl
}.

(* In order for a lattice implementation to be correct, each piece of
code in [ConcreteLattice] must compute exactly what we expect. We
specify that with the Hoare triples defined in [CodeTriples.v]. *)

Class WfConcreteLattice (T: Type) (L : JoinSemiLattice T) (CL: ConcreteLattice T) (E : Encodable T) :=
{ genBot_spec: forall Q,
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

Instance TMUHLwf : WfConcreteLattice Lab HL TMUHL EncodableHL :=
{ genBot_spec := genBot_spec_HL
; genJoin_spec := genJoin_spec_HL
; genFlows_spec := genFlows_spec_HL
}.
