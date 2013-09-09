Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import LibTactics.

Require Import Instr Memory.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import CodeSpecs.
Require Import CodeTriples.

Local Open Scope Z_scope.

Section fix_cblock.

Variable cblock : block privilege.
Variable stamp_cblock : Mem.stamp cblock = Kernel.

(* Lattice-dependent parameters *)
Class ConcreteLattice (T: Type) :=
{ labToVal :  T -> val privilege -> memory -> Prop
; valToLab :  val privilege -> memory -> T
; genBot : list Instr
; genJoin : list Instr
; genFlows : list Instr
}.

Local Open Scope Z_scope.

Instance TMUHL : ConcreteLattice Lab :=
{
  labToVal l z m :=
    match l with
      | L => Vint (boolToZ false) = z
      | H => Vint (boolToZ true) = z
    end

  ;valToLab z m :=
    match z with
      | Vint 0 => L
      | _ => H
    end

  ;genBot := genFalse

  ;genJoin := genOr

  ;genFlows := genImpl
}.

Definition mem_def_on_cache (m : memory) : Prop :=
  exists fr, Mem.get_frame m cblock = Some fr.

Lemma extends_mem_def_on_cache : forall m m',
                                   mem_def_on_cache m ->
                                   extends m m' ->
                                   mem_def_on_cache m'.
Proof.
  intros m m' H EXT.
  destruct H.
  econstructor; apply EXT; eauto.
Qed.

Inductive mem_eq_except_cache (m m' : memory) : Prop :=
| meec_intro :
    mem_def_on_cache m ->
    kernel_memory_extension cblock m m' ->
    mem_eq_except_cache m m'.

Class WfConcreteLattice (T: Type) (L : JoinSemiLattice T) (CL: ConcreteLattice T) :=
{ labToVal_cache : forall l z m m', labToVal l z m -> mem_eq_except_cache m m' -> labToVal l z m'
; labToVal_inj : forall l1 l2 z m, labToVal l1 z m -> labToVal l2 z m -> l1 = l2
; labToVal_valToLab_id : forall l z m, labToVal l z m -> valToLab z m = l
; labToVal_extension_comp : forall m1 m2 l z,  labToVal l z m1 -> extends m1 m2 ->
                                             mem_def_on_cache m1 ->
                                             labToVal l z m2
; genBot_spec: forall m0 (Hm0: mem_def_on_cache m0) (Q:memory->stack->Prop),
   HT cblock genBot
      (fun m s => extends m0 m /\
                  (forall m1 z t, extends m m1 -> labToVal bot z m1 -> Q m1 ((z,t):::s)))
      Q
; genJoin_spec:
    forall m0 (Hm0: mem_def_on_cache m0) (Q: memory-> stack->Prop),
       HT cblock genJoin
         (fun m s =>
          exists s0 l z t l' z' t',
             s = (z, t) ::: (z', t') ::: s0 /\
             extends m0 m /\
             labToVal l z m /\ labToVal l' z' m /\
             (forall m1 zz' t, extends m m1 -> labToVal (l \_/ l') zz' m1 ->
                         Q m1 ((zz', t) ::: s0)))
         Q

  (* NC: we could discharge this by implementing [genFlows] in terms of
   [genJoin], and using the fact that [flows l l' = true <-> join l l' = l']. *)
; genFlows_spec: forall m0 (Hm0: mem_def_on_cache m0) (Q: memory -> stack -> Prop),
                   HT  cblock genFlows
                       (fun m s =>
                          exists l l' z z' t t' s0,
                            extends m0 m /\
                            labToVal l z m /\ labToVal l' z' m /\
                            s = (z,t):::(z',t'):::s0 /\
                            forall t'',
                              Q m ((Vint (boolToZ(flows l l')),t''):::s0))
                       Q
}.

Section Spec_alt.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {WfCLatt: WfConcreteLattice T Latt CLatt}.

Lemma genBot_spec': forall I m0 (Hm0: mem_def_on_cache m0)
                      (Hext: extension_comp I),
                 HT cblock genBot
                    (fun m s => extends m0 m /\ I m s)
                    (fun m s =>
                       match s with
                           | CData (z,t)::tl => extends m0 m /\
                             I m tl /\ labToVal bot z m
                           | _ => False
                       end).
Proof.
  intros.
  eapply HT_strengthen_premise.
  eapply genBot_spec with (m1 := m0); eauto.
  intros. simpl.
  destruct H.
  intuition eauto.
  unfold extends; eauto.
Qed.

Lemma genJoin_spec': forall l l' I m0 (Hmem0: mem_def_on_cache m0)
                       (Hext: extension_comp I),
                  HT  cblock genJoin
                      (fun m s =>
                         match s with
                             | CData (z,t)::CData (z',t')::tl =>
                               labToVal l z m /\ labToVal l' z' m /\
                               extends m0 m /\ I m tl
                             | _ => False
                         end)
                      (fun m s =>
                         match s with
                             | CData (zz', t) :: tl =>
                               labToVal (join l l') zz' m /\
                               extends m0 m /\ I m tl
                             | _ => False
                         end).
Proof.
  intros.
  eapply HT_strengthen_premise.
  eapply genJoin_spec; eauto.
  go_match. do 7 eexists; intuition; eauto.
  unfold extends; eauto.
Qed.

Lemma genFlows_spec' : forall l l' I m0 (Hmem0: mem_def_on_cache m0)
                        (Hext: extension_comp I),
                   HT  cblock genFlows
                       (fun m s =>
                          match s with
                            | CData (z,t)::CData (z',t')::tl =>
                              labToVal l z m /\ labToVal l' z' m /\
                              extends m0 m /\ I m tl
                            | _ => False
                          end)
                       (fun m s =>
                          match s with
                            | CData (Vint z, t) :: tl =>
                              boolToZ (flows l l') = z /\
                              extends m0 m /\ I m tl
                            | _ => False
                          end).
Proof.
  intros.
  eapply HT_strengthen_premise.
  eapply genFlows_spec; eauto.
  go_match. do 7 eexists; intuition; eauto.
Qed.

End Spec_alt.

End fix_cblock.
