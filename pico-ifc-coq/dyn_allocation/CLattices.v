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
{ labToZ :  T -> Z -> memory -> Prop
; ZToLab :  Z -> memory -> T
; genBot : list Instr
; genJoin : list Instr
; genFlows : list Instr
}.

Local Open Scope Z_scope.

Instance TMUHL : ConcreteLattice Lab :=
{
  labToZ l z m :=
    match l with
      | L => boolToZ false = z
      | H => boolToZ true = z
    end

  ;ZToLab z m :=
    match z with
      | 0 => L
      | _ => H
    end

  ;genBot := genFalse

  ;genJoin := genOr

  ;genFlows := genImpl
}.

Inductive mem_def_on_cache (m : memory) : Prop :=
| mdoc_intro :
    forall opcode pctag tag1 tag2 tag3 tagr tagrpc,
      value_on_cache cblock m addrOpLabel (Vint opcode) ->
      value_on_cache cblock m addrTag1 (Vint tag1) ->
      value_on_cache cblock m addrTag2 (Vint tag2) ->
      value_on_cache cblock m addrTag3 (Vint tag3) ->
      value_on_cache cblock m addrTagPC (Vint pctag) ->
      value_on_cache cblock m addrTagRes tagr ->
      value_on_cache cblock m addrTagResPC tagrpc ->
      mem_def_on_cache m.

Lemma extends_mem_def_on_cache : forall m m',
                                   mem_def_on_cache m ->
                                   extends m m' ->
                                   mem_def_on_cache m'.
Proof.
  intros m m' H EXT.
  destruct H.
  repeat match goal with
           | H : value_on_cache _ _ _ _ |- _ => inv H
         end.
  econstructor; econstructor; apply EXT; eauto.
Qed.

Inductive mem_eq_except_cache (m m' : memory) : Prop :=
| meec_intro :
    mem_def_on_cache m ->
    (forall b addr v,
       b <> cblock ->
       load b addr m = Some v ->
       load b addr m' = Some v) ->
    mem_eq_except_cache m m'.

Class WfConcreteLattice (T: Type) (L : JoinSemiLattice T) (CL: ConcreteLattice T) :=
{ labToZ_cache : forall l z m m', labToZ l z m -> mem_eq_except_cache m m' -> labToZ l z m'
; labToZ_inj : forall l1 l2 z m, labToZ l1 z m -> labToZ l2 z m -> l1 = l2
; labToZ_ZToLab_id : forall l z m, labToZ l z m -> ZToLab z m = l
; labToZ_extension_comp : forall m1 m2 l z,  labToZ l z m1 -> extends m1 m2 ->
                                             mem_def_on_cache m1 ->
                                             labToZ l z m2
; genBot_spec: forall m0 (Hm0: mem_def_on_cache m0) (Q:memory->stack->Prop),
   HT cblock genBot
      (fun m s => extends m0 m /\
                  (forall m1 z, extends m m1 -> labToZ bot z m1 -> Q m1 ((Vint z,handlerTag):::s)))
      Q
; genJoin_spec:
    forall m0 (Hm0: mem_def_on_cache m0) (Q: memory-> stack->Prop),
       HT cblock genJoin
         (fun m s =>
          exists s0 l z t l' z' t',
             s = (Vint z, t) ::: (Vint z', t') ::: s0 /\
             extends m0 m /\
             labToZ l z m /\ labToZ l' z' m /\
             (forall m1 zz', extends m m1 -> labToZ (l \_/ l') zz' m1 ->
                         Q m1 ((Vint zz', handlerTag) ::: s0)))
         Q

  (* NC: we could discharge this by implementing [genFlows] in terms of
   [genJoin], and using the fact that [flows l l' = true <-> join l l' = l']. *)
; genFlows_spec: forall m0 (Hm0: mem_def_on_cache m0) (Q: memory -> stack -> Prop),
                   HT  cblock genFlows
                       (fun m s =>
                          exists l l' z z' t t' s0,
                            extends m0 m /\
                            labToZ l z m /\ labToZ l' z' m /\
                            s = (Vint z,t):::(Vint z',t'):::s0 /\
                            Q m ((Vint (boolToZ(flows l l')),handlerTag):::s0))
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
                           | CData (Vint z,t)::tl => extends m0 m /\
                             I m tl /\ labToZ bot z m /\ t = handlerTag
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
                             | CData (Vint z,t)::CData (Vint z',t')::tl =>
                               labToZ l z m /\ labToZ l' z' m /\
                               extends m0 m /\ I m tl
                             | _ => False
                         end)
                      (fun m s =>
                         match s with
                             | CData (Vint zz', t) :: tl =>
                               labToZ (join l l') zz' m /\
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
                            | CData (Vint z,t)::CData (Vint z',t')::tl =>
                              labToZ l z m /\ labToZ l' z' m /\
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
