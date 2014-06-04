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
Variable table : CSysTable.

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
   HT cblock table genBot
      (fun m s => extends m0 m /\
                  (forall m1 z t, extends m m1 -> labToVal bot z m1 -> Q m1 ((z,t):::s)))
      Q
; genJoin_spec:
    forall m0 (Hm0: mem_def_on_cache m0) (Q: memory-> stack->Prop),
       HT cblock table genJoin
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
                   HT  cblock table genFlows
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
                 HT cblock table genBot
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
                  HT  cblock table genJoin
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
                   HT  cblock table genFlows
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

Section Glue.

Import Vector.VectorNotations.

Local Open Scope nat_scope.


Definition nth_labToVal {n:nat} (vls: Vector.t T n) (s:nat) : val privilege -> memory -> Prop :=
  fun z m =>
    match le_lt_dec n s with
      | left _ => z = dontCare
      | right p => labToVal (Vector.nth_order vls p) z m
  end.

Lemma of_nat_lt_proof_irrel:
  forall (m n: nat) (p q: m < n),
    Fin.of_nat_lt p = Fin.of_nat_lt q.
Proof.
  induction m; intros.
    destruct n.
      false; omega.
      reflexivity.
    destruct n.
      false; omega.
      simpl; erewrite IHm; eauto.
Qed.

(* NC: this took a few tries ... *)
Lemma nth_order_proof_irrel:
  forall (m n: nat) (v: Vector.t T n) (p q: m < n),
    Vector.nth_order v p = Vector.nth_order v q.
Proof.
  intros.
  unfold Vector.nth_order.
  erewrite of_nat_lt_proof_irrel; eauto.
Qed.

Lemma nth_order_valid: forall (n:nat) (vls: Vector.t T n) m,
  forall (lt: m < n),
  nth_labToVal vls m = labToVal (Vector.nth_order vls lt).
Proof.
  intros.
  unfold nth_labToVal.
  destruct (le_lt_dec n m).
  false; omega.
  (* NC: Interesting: here we have two different proofs [m < n0] being
  used as arguments to [nth_order], and we need to know that the
  result of [nth_order] is the same in both cases.  I.e., we need
  proof irrelevance! *)
  erewrite nth_order_proof_irrel; eauto.
Qed.

Definition labsToVals {n:nat} (vls :Vector.t T n) (m: memory) :
  (val privilege * val privilege * val privilege) -> Prop :=
fun z0z1z2 =>
  let '(z0,z1,z2) := z0z1z2 in
  nth_labToVal vls 0 z0 m /\
  nth_labToVal vls 1 z1 m /\
  nth_labToVal vls 2 z2 m.

Lemma extension_comp_nth_labToVal : forall m1 m2 (n m:nat) (vls: Vector.t T n) z,
    nth_labToVal vls m z m1 ->
    extends m1 m2 ->
    mem_def_on_cache m1 ->
    nth_labToVal vls m z m2.
Proof.
  unfold nth_labToVal; intros.
  destruct (le_lt_dec n m); eauto.
  eapply labToVal_extension_comp; eauto.
Qed.

Lemma labsToVals_extension_comp :
  forall m1 m2 n (vls : Vector.t _ n) ts
         (Hvls : labsToVals vls m1 ts)
         (EXT : extends m1 m2)
         (DEF : mem_def_on_cache m1),
    labsToVals vls m2 ts.
Proof.
  unfold labsToVals.
  intros m1 m2 n vls [[t1 t2] t3].
  intuition;
  eapply extension_comp_nth_labToVal; eauto.
Qed.
Hint Resolve labsToVals_extension_comp.

Lemma labsToVals_cache :
  forall m1 m2 n (vls : Vector.t _ n) ts
         (Hvls : labsToVals vls m1 ts)
         (EQ : mem_eq_except_cache m1 m2),
  labsToVals vls m2 ts.
Proof.
  unfold labsToVals, nth_labToVal.
  intros.
  destruct ts as [[t1 t2] t3].
  destruct Hvls as (H1 & H2 & H3).
  repeat split;
  repeat match goal with
           | H : context[le_lt_dec n ?m] |- context[le_lt_dec n ?m] =>
             destruct (le_lt_dec n m); trivial
         end;
  eauto using labToVal_cache.
Qed.
Hint Resolve labsToVals_cache.

End Glue.

End Spec_alt.

End fix_cblock.
