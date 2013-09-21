Require Import EquivDec.
Require Import List.

Require Import Utils.
Require Import Lattices.

Require Import Instr.
Require Import AbstractCommon.
Require Import Memory.
Require Import AbstractMachine.
Require Import QuasiAbstractMachine.
Require Import Refinement.

Open Scope list_scope.

Set Implicit Arguments.

Section Refinement.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Definition match_tags (t1 t2 : T) (m2 : memory T unit) : Prop :=
  t1 = t2.
Hint Unfold match_tags.

Definition valid_update (m2 m2' : memory T unit) : Prop := True.
Hint Unfold valid_update.

Lemma valid_update_match_tags :
  forall t1 t2 m2 m2',
    match_tags t1 t2 m2 ->
    valid_update m2 m2' ->
    match_tags t1 t2 m2'.
Proof. eauto. Qed.

Notation meminj := (meminj T unit).
Notation Meminj := (Meminj T T T unit match_tags).
Notation match_atoms := (match_atoms T T T unit match_tags).
Notation match_vals := (match_vals T unit).
Notation update_meminj := (update_meminj T unit).

Hint Resolve match_vals_eq.
Hint Constructors Memory.match_atoms.
Hint Constructors Memory.match_vals.
Hint Resolve update_meminj_eq.

Inductive match_stk_elmt (mi : meminj) : StkElmt T T -> StkElmt T unit -> memory T unit -> Prop :=
| mse_data : forall a1 a2 m2
                    (ATOMS : match_atoms mi a1 a2 m2),
               match_stk_elmt mi (AData a1) (AData a2) m2
| mse_ret : forall pc b m2, match_stk_elmt mi (ARet pc b) (ARet pc b) m2.
Hint Constructors match_stk_elmt.

Definition match_stacks (mi : meminj) : list (StkElmt T T) -> list (StkElmt T unit) -> memory T unit -> Prop :=
  fun s1 s2 m2 => Forall2 (fun se1 se2 => match_stk_elmt mi se1 se2 m2) s1 s2.
Hint Unfold match_stacks.

Inductive match_states : @a_state T -> @qa_state T -> Prop :=
| aqa_intro : forall mi m1 m2 p stk1 stk2 pc
                     (INJ : Meminj m1 m2 mi)
                     (STK : match_stacks mi stk1 stk2 m2),
                match_states (AState m1 p stk1 pc) (AState m2 p stk2 pc).
Hint Constructors match_states.

Lemma alloc_match_stacks :
  forall size
         lab a1 m1 b1 m1'
         a2 m2 b2 m2'
         mi stk1 stk2
         (STK : match_stacks mi stk1 stk2 m2)
         (ALLOC1 : a_alloc size lab a1 m1 = Some (b1, m1'))
         (ALLOC2 : qa_alloc size a2 m2 = Some (b2, m2'))
         (INJ : Meminj m1 m2 mi),
    match_stacks (update_meminj mi b2 b1) stk1 stk2 m2'.
Proof.
  intros.
  induction STK; constructor; trivial.
  inv H; constructor.
  inv ATOMS. constructor; auto.
  inv VALS; constructor.
  rewrite update_meminj_neq; auto.
  eapply mi_valid in BLOCK; eauto.
  destruct BLOCK as [? [? [? [? ?]]]].
  unfold qa_alloc, alloc in ALLOC2.
  destruct (zreplicate size a2); inv ALLOC2.
  eapply Mem.alloc_get_fresh in H3; eauto.
  congruence.
Qed.

Lemma match_stacks_app :
  forall mi stk1 args2 stk2' m2
         (STKS : match_stacks mi stk1 (args2 ++ stk2') m2),
    exists args1 stk1',
      stk1 = args1 ++ stk1' /\
      match_stacks mi args1 args2 m2 /\
      match_stacks mi stk1' stk2' m2.
Proof.
  intros.
  gdep stk1.
  induction args2 as [|arg args2 IH]; intros stk1 STKS.
  - exists nil. exists stk1. eauto.
  - simpl in STKS.
    inv STKS.
    exploit IH; eauto.
    intros [? [? [? [? ?]]]]. subst.
    repeat eexists; eauto.
    trivial.
Qed.

Lemma match_stacks_length :
  forall mi stk1 stk2 m2
         (STKS : match_stacks mi stk1 stk2 m2),
    length stk1 = length stk2.
Proof. induction 1; simpl; eauto. Qed.
Hint Resolve match_stacks_length.

Lemma match_stacks_all_data :
  forall mi stk1 stk2 m2
         (STKS : match_stacks mi stk1 stk2 m2)
         (DATA : forall se2, In se2 stk2 -> exists a2, se2 = AData a2),
    forall se1, In se1 stk1 -> exists a1, se1 = AData a1.
Proof.
  induction 1 as [|se1 se2 stk1 stk2 STKELMT STKS IHSTKS]; intros; inv H.
  - inv STKELMT; eauto.
    specialize (DATA (ARet pc b)).
    destruct DATA; simpl; eauto.
    congruence.
  - apply IHSTKS; simpl in *; auto.
Qed.
Hint Resolve match_stacks_all_data.

Lemma match_stacks_app_2 :
  forall mi stk11 stk12 stk21 stk22 m2
         (STKS1 : match_stacks mi stk11 stk21 m2)
         (STKS2 : match_stacks mi stk12 stk22 m2),
    match_stacks mi (stk11 ++ stk12) (stk21 ++ stk22) m2.
Proof. intros. eauto using Forall2_app. Qed.
Hint Resolve match_stacks_app_2.

Hint Constructors pop_to_return.

Lemma match_stacks_pop_to_return :
  forall mi stk1 stk2 stk2' pc b m2
         (STKS : match_stacks mi stk1 stk2 m2)
         (POP : pop_to_return stk2 (ARet pc b :: stk2')),
    exists stk1',
      pop_to_return stk1 (ARet pc b :: stk1') /\
      match_stacks mi stk1' stk2' m2.
Proof.
  intros.
  gdep stk2.
  induction stk1 as [|se1 stk1 IH]; intros;
  inv POP; inv STKS;
  match goal with
    | H : match_stk_elmt _ _ _ _ |- _ =>
      inv H; eauto
  end.
  exploit IH; eauto.
  intros [? [? ?]].
  eauto.
Qed.

Lemma match_stacks_index_list :
  forall mi n s1 s2 x2 m2
         (IDX : index_list n s2 = Some x2)
         (STKS : match_stacks mi s1 s2 m2),
    exists x1,
      index_list n s1 = Some x1 /\
      match_stk_elmt mi x1 x2 m2.
Proof.
  induction n as [|n IH]; intros; inv STKS; simpl in *; allinv; eauto.
Qed.

Lemma match_stacks_update_list :
  forall mi n se1 s1 se2 s2 s2' m2
         (STKS : match_stacks mi s1 s2 m2)
         (STKELMTS : match_stk_elmt mi se1 se2 m2)
         (UPD : update_list n se2 s2 = Some s2'),
    exists s1',
      update_list n se1 s1 = Some s1' /\
      match_stacks mi s1' s2' m2.
Proof.
  intros mi n.
  induction n as [|n IH]; intros; inv STKS; simpl in *; try congruence;
  allinv; eauto.
  match goal with
    | H : (match ?UP with _ => _ end) = Some _ |- _ =>
      destruct UP as [s2''|] eqn:?; try congruence
  end.
  allinv.
  exploit (@IH se1); eauto.
  intros [s1'' [EQ ?]].
  rewrite EQ.
  eauto.
Qed.

Lemma match_stacks_swap :
  forall mi n s1 s2 s2' m2
         (SWAP : swap n s2 = Some s2')
         (STKS : match_stacks mi s1 s2 m2),
    exists s1',
      swap n s1 = Some s1' /\
      match_stacks mi s1' s2' m2.
Proof.
  unfold swap.
  intros.
  destruct s2 as [|se2 s2]; try congruence.
  destruct (index_list n (se2 :: s2)) as [se2'|] eqn:IDX2; try congruence.
  exploit match_stacks_index_list; eauto.
  intros [se1' [IDX1 STKELMTS]].
  inversion STKS as [|se1 ?]; subst.
  rewrite IDX1.
  eapply match_stacks_update_list; eauto.
Qed.

Lemma match_atoms_mem_irrel :
  forall mi a1 a2 m2 m2'
         (ATOMS : match_atoms mi a1 a2 m2),
    match_atoms mi a1 a2 m2'.
Proof. intros. inv ATOMS; eauto. Qed.
Hint Resolve match_atoms_mem_irrel : mem_irrel.

Lemma match_stk_elmt_mem_irrel :
  forall mi se1 se2 m2 m2'
         (STKELMT : match_stk_elmt mi se1 se2 m2),
    match_stk_elmt mi se1 se2 m2'.
Proof. intros. inv STKELMT; eauto with mem_irrel. Qed.
Hint Resolve match_stk_elmt_mem_irrel : mem_irrel.

Lemma match_stacks_mem_irrel :
  forall mi s1 s2 m2 m2'
         (STKS : match_stacks mi s1 s2 m2),
    match_stacks mi s1 s2 m2'.
Proof. intros. induction STKS; eauto with mem_irrel. Qed.
Hint Resolve match_stacks_mem_irrel : mem_irrel.

Hint Unfold a_alloc.
Hint Unfold qa_alloc.

Inductive match_asyscalls : ASysCall T T -> ASysCall T unit -> Prop :=
| masc_intro : forall ar f1 f2
                      (EXT : forall mi args1 args2 m2,
                               Forall2 (fun arg1 arg2 => match_atoms mi arg1 arg2 m2)
                                       args1 args2 ->
                               match_options (fun a1 a2 => match_atoms mi a1 a2 m2)
                                             (f1 args1) (f2 args2)),
                 match_asyscalls {| asi_arity := ar; asi_sem := f1 |}
                                 {| asi_arity := ar; asi_sem := f2 |}.

Inductive match_asystables : ASysTable T T -> ASysTable T unit -> Prop :=
| mast_intro : forall t1 t2
                      (MATCH : forall id, match_options match_asyscalls (t1 id) (t2 id)),
                 match_asystables t1 t2.

Variable t1 : ASysTable T T.
Variable t2 : ASysTable T unit.
Hypothesis Ht1t2 : match_asystables t1 t2.

Ltac inv_match :=
  repeat match goal with
           | STK : Forall2 _ _ nil |- _ => inv STK
           | STK : Forall2 _ _ (_ :: _) |- _ => inv STK
           | STKELMT : match_stk_elmt _ _ _ _ |- _ => inv STKELMT
           | ATOMS : match_atoms _ _ (_,_) _ |- _ => inv ATOMS
           | VALS : match_vals _ _ (Vint _) |- _ => inv VALS
           | VALS : match_vals _ _ (Vptr _ _) |- _ => inv VALS
           | TAGS : match_tags _ _ _ |- _ => unfold match_tags in TAGS; subst
         end.

Lemma match_stacks_map_adata :
  forall mi stk1 args2 m2
         (MATCH : match_stacks mi stk1 (map AData args2) m2),
  exists args1,
    stk1 = map AData args1 /\
    Forall2 (fun a1 a2 => match_atoms mi a1 a2 m2) args1 args2.
Proof.
  unfold match_stacks.
  intros.
  gdep stk1.
  induction args2 as [|a2 args2 IH]; simpl; intros; inv_match.
  - eexists nil. simpl. intuition.
  - exploit IH; eauto.
    intros (args1 & ? & MATCH). subst.
    eexists (a1 :: args1). eauto.
Qed.

(* MOVE *)
Lemma Forall2_length :
  forall A B (R : A -> B -> Prop) l1 l2,
    Forall2 R l1 l2 -> length l1 = length l2.
Proof.
  induction 1; eauto; simpl; congruence.
Qed.

Lemma a_qa_simulation :
  forall s1 s2 e s2'
         (STEP : step_rules fetch_rule t2 s2 e s2')
         (MATCH : match_states s1 s2),
    exists s1',
      a_step t1 s1 e s1' /\
      match_states s1' s2'.
Proof.
  intros.
  inv Ht1t2.
  inv STEP;
  inv MATCH;
  unfold match_stacks in *;
  inv_match;
  match goal with
    | H : run_tmr _ _ _ _ = Some _ |- _ =>
      unfold run_tmr, Rules.apply_rule in H; simpl in H;
      unfold Vector.nth_order in H; simpl in H
    | INSTR : context[SysCall ?id],
      MATCH : context[match_asyscalls],
      TABLE : t2 ?id = Some _ |- _ =>
      specialize (MATCH id);
      rewrite TABLE in MATCH;
      inv MATCH
  end;
  try match goal with
        | MATCH : match_asyscalls _ _ |- _ =>
          inv MATCH
      end;
  simpl in *; unfold Vector.nth_order; simpl;
  try congruence;
  repeat match goal with
           | H : context[if ?b then _ else _] |- _ =>
             destruct b eqn:?; simpl in H
           | H : Some _ = Some _ |- _ => inv H
           | H : _ === _ |- _ => compute in H; subst
           | H1 : ?x = ?a,
             H2 : ?x = ?b |- _ =>
             assert (a = b) by congruence; clear H2
         end;
  try congruence;

  try match goal with
        | H : add _ _ = Some _ |- _ =>
          exploit add_defined; eauto; intros [? [? ?]]
        | SUB : sub _ _ = Some _ |- _ =>
          exploit (sub_defined T unit); eauto; intros [? [? ?]]
        | H : qa_alloc _ _ _ = Some _ |- _ =>
          exploit (meminj_alloc T T T unit _ _ valid_update_match_tags); eauto;
          try solve [constructor; eauto];
          intros [? [? [? ?]]];
          exploit alloc_match_stacks; eauto; intro
        | H : load _ _ _ = Some _ |- _ =>
          exploit meminj_load; eauto; intros [[? ?] [? H']];
          inv H'; inv_match
        | H : Forall2 _ _ (_ ++ _) |- _ =>
          exploit match_stacks_app; eauto; intros [? [? [? [? ?]]]]; subst
        | H : pop_to_return _ _ |- _ =>
          exploit match_stacks_pop_to_return; eauto; intros [? [? ?]]
      end;

  (* For some weird reason, trying to merge this match with the previous one doesn't work. *)
  try match goal with
        | H : store _ _ _ _ = Some _ |- _ =>
          exploit (meminj_store T T T unit _ _ valid_update_match_tags);
          eauto; try solve [econstructor; eauto]; intros [? [? ?]]
        | H : swap _ _ = Some _ |- _ =>
          exploit match_stacks_swap; eauto; intros [? [? ?]]
        | H1 : Forall2 _ _ _,
          H2 : index_list _ _ = Some _ |- _ =>
          exploit match_stacks_index_list; eauto; intros [? [? ?]]
        | H : context[SysCall _],
          EXT : context[match_options _ _ _] |- _ =>
          exploit match_stacks_map_adata; eauto; intros (? & ? & ?); subst;
          exploit EXT; eauto; intros RES;
          match goal with
            | RES : match_options _ ?r1 ?r2,
              EQ : ?r2 = Some _ |- _ =>
              rewrite EQ in RES; inv RES
          end
      end;

  (* Always using mem_irrel causes spurious existentials to be generated *)
  solve [eexists; split; econstructor (simpl; solve [eauto 7 using Forall2_length
                                                    |eauto 7 with mem_irrel])].

Qed.

Program Definition abstract_quasi_abstract_sref :=
  @strong_refinement (abstract_machine t1)
                     (tini_quasi_abstract_machine t2)
                     eq match_states _.
Next Obligation.
  exploit a_qa_simulation; eauto.
  intros [? [? ?]].
  repeat eexists; eauto.
  destruct e2; constructor; auto.
Qed.

Definition emptyinj : meminj := fun _ => None.
Hint Unfold emptyinj.

Definition emptyinj_meminj :
  Meminj (Mem.empty _ _) (Mem.empty _ _) emptyinj.
Proof.
  unfold emptyinj.
  constructor; simpl; congruence.
Qed.
Hint Resolve emptyinj_meminj.

Lemma match_init_stacks: forall m2 d1,
 match_stacks emptyinj
              (map (fun a : PcAtom T => let (i,l) := a in AData (Vint i,l)) d1)
              (map (fun a : PcAtom T => let (i,l) := a in AData (Vint i,l)) d1)
              m2.
Proof.
  induction d1 as [|[xv xl] d1 IH]; intros;
  (simpl; constructor; auto).
Qed.
Hint Resolve match_init_stacks.

Program Definition abstract_quasi_abstract_ref :=
  @refinement_from_state_refinement (abstract_machine t1)
                                    (tini_quasi_abstract_machine t2)
                                    abstract_quasi_abstract_sref eq
                                    _.

Next Obligation.
  destruct i2 as [[p d] def]. simpl.
  econstructor; eauto.
Qed.

End Refinement.
