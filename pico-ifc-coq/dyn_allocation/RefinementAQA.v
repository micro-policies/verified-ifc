Require Import EquivDec.
Require Import List.

Require Import Utils.
Require Import Lattices.

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

Notation meminj := (meminj T unit).
Notation Meminj := (Meminj T T T unit eq).
Notation match_atoms := (match_atoms T T T unit eq).
Notation match_vals := (match_vals T unit).
Notation update_meminj := (update_meminj T unit).

Hint Resolve match_vals_eq.
Hint Constructors Memory.match_atoms.
Hint Constructors Memory.match_vals.
Hint Resolve update_meminj_eq.

Inductive match_stk_elmt (mi : meminj) : StkElmt T T -> StkElmt T unit -> Prop :=
| mse_data : forall a1 a2
                    (ATOMS : match_atoms mi a1 a2),
               match_stk_elmt mi (AData a1) (AData a2)
| mse_ret : forall pc b, match_stk_elmt mi (ARet pc b) (ARet pc b).
Hint Constructors match_stk_elmt.

Definition match_stacks (mi : meminj) : list (StkElmt T T) -> list (StkElmt T unit) -> Prop :=
  Forall2 (match_stk_elmt mi).
Hint Unfold match_stacks.

Inductive match_states : @a_state T -> @qa_state T -> Prop :=
| aqa_intro : forall mi m1 m2 p stk1 stk2 pc
                     (INJ : Meminj m1 m2 mi)
                     (STK : match_stacks mi stk1 stk2),
                match_states (AState m1 p stk1 pc) (AState m2 p stk2 pc).
Hint Constructors match_states.

Lemma alloc_match_stacks :
  forall size
         lab a1 m1 b1 m1'
         a2 m2 b2 m2'
         mi stk1 stk2
         (STK : match_stacks mi stk1 stk2)
         (ALLOC1 : a_alloc size lab a1 m1 = Some (b1, m1'))
         (ALLOC2 : qa_alloc size a2 m2 = Some (b2, m2'))
         (INJ : Meminj m1 m2 mi),
    match_stacks (update_meminj mi b2 b1) stk1 stk2.
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
  forall mi stk1 args2 stk2'
         (STKS : match_stacks mi stk1 (args2 ++ stk2')),
    exists args1 stk1',
      stk1 = args1 ++ stk1' /\
      match_stacks mi args1 args2 /\
      match_stacks mi stk1' stk2'.
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
  forall mi stk1 stk2
         (STKS : match_stacks mi stk1 stk2),
    length stk1 = length stk2.
Proof. induction 1; simpl; eauto. Qed.
Hint Resolve match_stacks_length.

Lemma match_stacks_all_data :
  forall mi stk1 stk2
         (STKS : match_stacks mi stk1 stk2)
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
  forall mi stk11 stk12 stk21 stk22
         (STKS1 : match_stacks mi stk11 stk21)
         (STKS2 : match_stacks mi stk12 stk22),
    match_stacks mi (stk11 ++ stk12) (stk21 ++ stk22).
Proof. intros. eauto using Forall2_app. Qed.
Hint Resolve match_stacks_app_2.

Hint Constructors pop_to_return.

Lemma match_stacks_pop_to_return :
  forall mi stk1 stk2 stk2' pc b
         (STKS : match_stacks mi stk1 stk2)
         (POP : pop_to_return stk2 (ARet pc b :: stk2')),
    exists stk1',
      pop_to_return stk1 (ARet pc b :: stk1') /\
      match_stacks mi stk1' stk2'.
Proof.
  intros.
  gdep stk2.
  induction stk1 as [|se1 stk1 IH]; intros;
  inv POP; inv STKS;
  match goal with
    | H : match_stk_elmt _ _ _ |- _ =>
      inv H; eauto
  end.
  exploit IH; eauto.
  intros [? [? ?]].
  eauto.
Qed.

Lemma match_stacks_index_list :
  forall mi n s1 s2 x2
         (IDX : index_list n s2 = Some x2)
         (STKS : match_stacks mi s1 s2),
    exists x1,
      index_list n s1 = Some x1 /\
      match_stk_elmt mi x1 x2.
Proof.
  induction n as [|n IH]; intros; inv STKS; simpl in *; allinv; eauto.
Qed.

Lemma match_stacks_update_list :
  forall mi n se1 s1 se2 s2 s2'
         (STKS : match_stacks mi s1 s2)
         (STKELMTS : match_stk_elmt mi se1 se2)
         (UPD : update_list n se2 s2 = Some s2'),
    exists s1',
      update_list n se1 s1 = Some s1' /\
      match_stacks mi s1' s2'.
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
  forall mi n s1 s2 s2'
         (SWAP : swap n s2 = Some s2')
         (STKS : match_stacks mi s1 s2),
    exists s1',
      swap n s1 = Some s1' /\
      match_stacks mi s1' s2'.
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

Hint Unfold a_alloc.
Hint Unfold qa_alloc.

Lemma a_qa_simulation :
  forall s1 s2 e s2'
         (STEP : step_rules fetch_rule s2 e s2')
         (MATCH : match_states s1 s2),
    exists s1',
      a_step s1 e s1' /\
      match_states s1' s2'.
Proof.
  intros.
  inv STEP;
  inv MATCH;
  unfold match_stacks in *;
  match goal with
    | H : run_tmr _ _ _ _ = Some _ |- _ =>
      unfold run_tmr, Rules.apply_rule in H; simpl in H;
      unfold Vector.nth_order in H; simpl in H
  end;
  repeat match goal with
           | STK : Forall2 _ _ (_ :: _) |- _ => inv STK
           | STKELMT : match_stk_elmt _ _ _ |- _ => inv STKELMT
           | ATOMS : match_atoms _ _ (_,_) |- _ => inv ATOMS
           | VALS : match_vals _ _ (Vint _) |- _ => inv VALS
           | VALS : match_vals _ _ (Vptr _ _) |- _ => inv VALS
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
          exploit (meminj_alloc T T T unit); eauto;
          try solve [constructor; eauto];
          intros [? [? [? ?]]];
          exploit alloc_match_stacks; eauto; intro
        | H : load _ _ _ = Some _ |- _ =>
          exploit meminj_load; eauto; intros [[? ?] [? H']];
          inv H'
        | H : Forall2 _ _ (_ ++ _) |- _ =>
          exploit match_stacks_app; eauto; intros [? [? [? [? ?]]]]; subst
        | H : pop_to_return _ _ |- _ =>
          exploit match_stacks_pop_to_return; eauto; intros [? [? ?]]
      end;

  (* For some weird reason, trying to merge this match with the previous one doesn't work. *)
  try match goal with
        | H : store _ _ _ _ = Some _ |- _ =>
          exploit (meminj_store T T T unit); eauto; try solve [econstructor; eauto]; intros [? [? ?]]
        | H : swap _ _ = Some _ |- _ =>
          exploit match_stacks_swap; eauto; intros [? [? ?]]
        | H1 : Forall2 _ _ _,
          H2 : index_list _ _ = Some _ |- _ =>
          exploit match_stacks_index_list; eauto; intros [? [? ?]]
      end;

  solve [eexists; split; econstructor (solve [simpl; eauto 7])].

Qed.

Program Definition abstract_quasi_abstract_sref :=
  @strong_refinement abstract_machine
                     tini_quasi_abstract_machine
                     eq match_states _.
Next Obligation.
  exploit a_qa_simulation; eauto.
  intros [? [? ?]].
  eauto.
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

Lemma match_init_stacks: forall d1,
 match_stacks emptyinj
              (map (fun a : PcAtom T => let (i,l) := a in AData (Vint i,l)) d1)
              (map (fun a : PcAtom T => let (i,l) := a in AData (Vint i,l)) d1).
Proof.
  induction d1 as [|[xv xl] d1 IH]; intros;
  (simpl; constructor; auto).
Qed.
Hint Resolve match_init_stacks.

Program Definition abstract_quasi_abstract_ref :=
  @refinement_from_state_refinement abstract_machine tini_quasi_abstract_machine
                                    abstract_quasi_abstract_sref eq
                                    _.

Next Obligation.
  destruct i2 as [[p d] def]. simpl.
  econstructor; eauto.
Qed.

End Refinement.
