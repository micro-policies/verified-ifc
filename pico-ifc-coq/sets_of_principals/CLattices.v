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

Definition mem_def_on_cache (m : list (@Atom Z)) : Prop :=
  exists opcode pctag tag1 tag2 tag3 tagr tagrpc,
    tag_in_mem m addrOpLabel opcode /\
    tag_in_mem m addrTag1 tag1 /\
    tag_in_mem m addrTag2 tag2 /\
    tag_in_mem m addrTag3 tag3 /\
    tag_in_mem m addrTagPC pctag /\
    tag_in_mem' m addrTagRes tagr /\
    tag_in_mem' m addrTagResPC tagrpc.

Lemma extends_mem_def_on_cache : forall m m',
                                     mem_def_on_cache m ->
                                     extends m m' ->
                                     mem_def_on_cache m'.
Proof.
  intros. destruct H as [op [pctag [tag1 [tag2 [tag3 [tagr [tagrpc Hint]]]]]]].
  intuition.
  econstructor.
  unfold extends in *.
  repeat match goal with 
      | H: tag_in_mem _ _ _ |- _ => inv H
      | H: tag_in_mem' _ _ _ |- _ => inv H
  end.
  do 6 eexists; intuition; repeat (econstructor; eauto).
Qed.
Hint Resolve extends_mem_def_on_cache.

Definition mem_eq_except_cache (m m': list (@Atom Z)) : Prop := 
  mem_def_on_cache m /\
  forall addr, 
    addr <> addrOpLabel ->  addr <> addrTagPC -> 
    addr <> addrTag1 -> addr <> addrTag2 -> addr <> addrTag3 ->
    addr <> addrTagRes -> addr <> addrTagResPC -> 
    forall v, read_m addr m = Some v -> read_m addr m' = Some v.

Class WfConcreteLattice (T: Type) (L : JoinSemiLattice T) (CL: ConcreteLattice T) (SysTable:syscall_table T) :=
{ labToZ_cache : forall l z m m', labToZ l z m -> mem_eq_except_cache m m' -> labToZ l z m'
; labToZ_inj : forall l1 l2 z m, labToZ l1 z m -> labToZ l2 z m -> l1 = l2
; labToZ_ZToLab_id : forall l z m, labToZ l z m -> ZToLab z m = l
; labToZ_extension_comp : forall m1 m2 l z,  labToZ l z m1 -> extends m1 m2 ->
                                             mem_def_on_cache m1 ->
                                             labToZ l z m2
; genBot_spec: forall m0 (Hm0: mem_def_on_cache m0) (Q:memory->stack->Prop),
   HT SysTable genBot
      (fun m s => extends m0 m /\ 
                  (forall m1 z, extends m m1 -> labToZ bot z m1 -> Q m1 ((z,handlerTag):::s)))
      Q
; genJoin_spec: 
    forall m0 (Hm0: mem_def_on_cache m0) (Q: memory-> stack->Prop),
       HT SysTable genJoin
         (fun m s =>
          exists s0 l z l' z',
             s = (z, handlerTag) ::: (z', handlerTag) ::: s0 /\
             extends m0 m /\
             labToZ l z m /\ labToZ l' z' m /\
             (forall m1 zz', extends m m1 -> labToZ (l \_/ l') zz' m1 ->
                         Q m1 ((zz', handlerTag) ::: s0)))
         Q

  (* NC: we could discharge this by implementing [genFlows] in terms of
   [genJoin], and using the fact that [flows l l' = true <-> join l l' = l']. *)
; genFlows_spec: forall m0 (Hm0: mem_def_on_cache m0) (Q: memory -> stack -> Prop),
                   HT  SysTable genFlows
                       (fun m s =>
                          exists l l' z z' s0,
                            extends m0 m /\
                            labToZ l z m /\ labToZ l' z' m /\
                            s = (z,handlerTag):::(z',handlerTag):::s0 /\
                            Q m ((boolToZ(flows l l'),handlerTag):::s0))
                       Q
}.


Section Spec_alt.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {SysTable : syscall_table T}
        {WfCLatt: WfConcreteLattice T Latt CLatt SysTable}.

Notation HT := (HT SysTable).
Notation HTEscape := (HTEscape SysTable).

Lemma genBot_spec': forall I m0 (Hm0: mem_def_on_cache m0)
                      (Hext: extension_comp I),
                 HT genBot 
                    (fun m s => extends m0 m /\ I m s)
                    (fun m s => 
                       match s with 
                           | CData (z,t)::tl => extends m0 m /\
                             I m tl /\ labToZ bot z m /\ t = handlerTag
                           | _ => False
                       end).
Proof.
  intros.
  eapply HT_strengthen_premise.
  eapply genBot_spec; eauto.
  intros. simpl. intuition; eauto.
  unfold extends; eauto.
Qed.

Lemma genJoin_spec': forall l l' I m0 (Hmem0: mem_def_on_cache m0)
                       (Hext: extension_comp I),
                  HT  genJoin
                      (fun m s => 
                         match s with 
                             | CData (z,t)::CData (z',t')::tl =>
                               labToZ l z m /\ labToZ l' z' m /\
                               t = handlerTag /\ t' = handlerTag /\
                               extends m0 m /\ I m tl
                             | _ => False
                         end)
                      (fun m s => 
                         match s with 
                             | CData (zz', t) :: tl =>
                               labToZ (join l l') zz' m /\
                               t = handlerTag /\
                               extends m0 m /\ I m tl 
                             | _ => False
                         end).
Proof.
  intros.
  eapply HT_strengthen_premise.
  eapply genJoin_spec; eauto.
  go_match. do 5 eexists; intuition; eauto.
  unfold extends; eauto.
Qed.

Lemma genFlows_spec' : forall l l' I m0 (Hmem0: mem_def_on_cache m0)
                        (Hext: extension_comp I),
                   HT  genFlows
                       (fun m s => 
                          match s with 
                            | CData (z,t)::CData (z',t')::tl =>
                              labToZ l z m /\ labToZ l' z' m /\
                              t = handlerTag  /\ t' = handlerTag /\
                              extends m0 m /\ I m tl
                            | _ => False
                          end)
                       (fun m s => 
                          match s with 
                            | CData (z, t) :: tl =>
                              boolToZ (flows l l') = z /\
                              t = handlerTag /\
                              extends m0 m /\ I m tl
                            | _ => False
                          end).
Proof.
  intros.
  eapply HT_strengthen_premise.
  eapply genFlows_spec; eauto.
  go_match. do 5 eexists; intuition; eauto.
Qed.

End Spec_alt.

(*
Local Open Scope Z_scope. 

Lemma labToZ_cache_HL : forall l z m m', labToZ l z m -> mem_eq_except_cache m m' -> labToZ l z m.
  simpl. intros.
  destruct l; congruence.
Qed.

Lemma labToZ_inj_HL : forall l1 l2 z m, labToZ l1 z m -> labToZ l2 z m -> l1 = l2.
Proof.
  simpl. intros.
  destruct l1, l2; congruence.
Qed.

Lemma labToZ_extension_comp_HL : forall m1 m2 l z,  labToZ l z m1 -> 
                                                    extends m1 m2 -> 
                                                    mem_def_on_cache m1 -> 
                                                    labToZ l z m2.
Proof.
  simpl. intros.
  destruct l; congruence.
Qed.

Lemma genBot_spec_HL : forall m0 (Hm0: mem_def_on_cache m0) (Q:memory->stack->Prop),
   HT genBot
      (fun m s => extends m0 m /\ 
                  (forall m1 z, 
                     extends m m1 -> labToZ bot z m1 -> Q m1 ((z,handlerTag):::s)))
      Q.
Proof.
  intros.
  unfold genBot, TMUHL. simpl. 
  eapply HT_strengthen_premise.
  eapply (genFalse_spec_wp); eauto. 
  intros. intuition. eapply H1; eauto.
  unfold extends; eauto.
Qed.

Lemma genJoin_spec_HL: forall m0 (Hm0: mem_def_on_cache m0) (Q: memory-> stack->Prop),
       HT genJoin
         (fun m s =>
          exists s0 l z l' z',
             s = (z, handlerTag) ::: (z', handlerTag) ::: s0 /\
             extends m0 m /\
             labToZ l z m /\ labToZ l' z' m /\
             (forall m1 zz', extends m m1 -> labToZ (l \_/ l') zz' m1 ->
                         Q m1 ((zz', handlerTag) ::: s0)))
         Q.
Proof.
  unfold genJoin, TMUHL. intros.
  unfold labToZ.
  eapply HT_strengthen_premise.
  eapply genOr_spec_wp; eauto.
  go_match. destruct H as [s0 [l [z [l' [z' Hint]]]]]. intuition.
  substs.
  cases l; cases l' ; substs;
  try solve
      [ exists true; exists true; exists s0 ; 
               intuition; simpl; try (eapply H4; eauto); 
               unfold extends; eauto
      | exists false; exists true; exists s0 ; 
               intuition; simpl; try (eapply H4; eauto);
               unfold extends; eauto
      | exists false; exists false; exists s0 ; 
               intuition; simpl; try (eapply H4; eauto);
               unfold extends; eauto
      | exists true; exists false; exists s0 ; 
               intuition; simpl; try (eapply H4; eauto);
               unfold extends; eauto ].
Qed.

Lemma genFlows_spec_HL: 
  forall m0 (Hm0: mem_def_on_cache m0) (Q: memory -> stack -> Prop),
                   HT  genFlows
                       (fun m s =>
                          exists l l' z z' s0,
                            extends m0 m /\
                            labToZ l z m /\ labToZ l' z' m /\
                            s = (z,handlerTag):::(z',handlerTag):::s0 /\
                            Q m ((boolToZ(flows l l'),handlerTag):::s0))
                       Q.
Proof.
  unfold genFlows, TMUHL. intros.
  eapply HT_strengthen_premise. 
  eapply genImpl_spec_wp; eauto.
  go_match. 
  destruct H as [l [l' [z [z' [s0 Hint]]]]]. intuition. substs.
  cases l; cases l' ; substs;
  try solve
      [ exists true; exists true; exists s0 ; 
               intuition; simpl; try (eapply H4; eauto); 
               unfold extends; eauto
      | exists false; exists true; exists s0 ; 
               intuition; simpl; try (eapply H4; eauto);
               unfold extends; eauto
      | exists false; exists false; exists s0 ; 
               intuition; simpl; try (eapply H4; eauto);
               unfold extends; eauto
      | exists true; exists false; exists s0 ; 
               intuition; simpl; try (eapply H4; eauto);
               unfold extends; eauto ].
Qed.  

Lemma labToZ_ZToLab_id_HL : forall l z m, 
                           labToZ l z m ->
                           ZToLab z m = l.
Proof.
  simpl. intros. destruct l, z; auto; try congruence.
Qed.

Instance TMUHLwf : WfConcreteLattice Lab HL TMUHL :=
{ labToZ_cache:= labToZ_cache_HL
; labToZ_ZToLab_id := labToZ_ZToLab_id_HL
; labToZ_inj := labToZ_inj_HL
; labToZ_extension_comp := labToZ_extension_comp_HL
; genBot_spec := genBot_spec_HL
; genJoin_spec := genJoin_spec_HL
; genFlows_spec := genFlows_spec_HL
}.


*)