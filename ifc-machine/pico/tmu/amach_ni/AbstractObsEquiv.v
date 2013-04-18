Require Setoid.
Require RelationClasses.
Require Import List.
Require Import Relations.
Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import Abstract.
Require Import ZArith.

Set Implicit Arguments.

Section ObsEquiv.

Context {Label: Type}.
Context {Latt: JoinSemiLattice Label}.

(** * Low equivalence relations *)
Inductive low_equiv_atom (o: Label) : relation (@Atom Label) := 
| le_a_low : forall l v, l <: o = true -> low_equiv_atom o (v,l) (v,l)
| le_a_high: forall l1 l2 v1 v2, 
  l1 <: o = false -> 
  l2 <: o = false ->
  low_equiv_atom o (v1,l1) (v2,l2).
Hint Constructors low_equiv_atom.

Global Instance low_atom (o: Label) : @Equivalence (@Atom Label) (low_equiv_atom o).
Proof.
  constructor.
  (* reflexive *) intro x. destruct x; 
  destruct (flows_dec l o); auto.
  (* symmetric *) intros x y Hxy. inv Hxy ; auto.
  (* transitive *) intros x y z Hxy Hyz. 
  inv Hxy; auto. inv Hyz ; auto. 
Qed.

Hint Extern 1 => 
  match goal with 
    | |- low_equiv_atom _ _ _ => reflexivity
  end.


Lemma low_equiv_atom_join_value: 
  forall o v1 v0 v v2 vl vl0  vl2 vl1, 
    low_equiv_atom o (v1, vl) (v, vl0) ->
    low_equiv_atom o (v2, vl2) (v0, vl1) ->
    low_equiv_atom o (v1, vl \_/ vl2) (v, vl0 \_/ vl1).
Proof.
  intros.
  inv H; inv H0; econstructor; eauto with lat.
Qed.

Inductive low_equiv_stkelt (o: Label) : @StkElmt Label -> @StkElmt Label -> Prop := 
| le_data : forall a1 a2
  (LEa: low_equiv_atom o a1 a2),
  low_equiv_stkelt o (AData a1) (AData a2)
| le_aret : forall a1 a2 b
  (LEa: low_equiv_atom o a1 a2),
  low_equiv_stkelt o (ARet a1 b) (ARet a2 b).
Hint Constructors low_equiv_stkelt.

Global Instance low_stkelt (o: Label) : @Equivalence (@StkElmt Label) (low_equiv_stkelt o).
Proof.
  constructor.
  (* reflexive *) intro x. destruct x; auto.
  (* symmetric *) intros x y Hxy. inv Hxy ; constructor ; symmetry; auto.
  (* transitive *) intros x y z Hxy Hyz. 
  inv Hxy; inv Hyz; constructor; etransitivity; eauto. 
Qed.

Hint Extern 1 => 
  match goal with 
    | |- low_equiv_stkelt _ _ _ => reflexivity
  end.
  
Inductive low_equiv_instr (o: Label) : Instr -> Instr -> Prop := 
| lei_noop : low_equiv_instr o Noop Noop  
| lei_add : low_equiv_instr o Add Add  
| lei_sub : low_equiv_instr o Sub Sub
| lei_load : low_equiv_instr o Load Load  
| lei_store : low_equiv_instr o Store Store
| lei_push : forall i,  low_equiv_instr o (Push i) (Push i)
| lei_jump : low_equiv_instr o Jump Jump
| lei_branchNZ : forall ofs, low_equiv_instr o (BranchNZ ofs) (BranchNZ ofs)
| lei_call : forall mpc b, low_equiv_instr o (Call mpc b) (Call mpc b)
| lei_return: low_equiv_instr o Ret Ret
| lei_vreturn: low_equiv_instr o VRet VRet
| lei_halt: low_equiv_instr o Halt Halt.
Hint Constructors low_equiv_instr.

Global Instance low_instr (o: Label) : @Equivalence Instr (low_equiv_instr o).
Proof.
  constructor.
  (* reflexive *) intro x. destruct x; auto.
  (* symmetric *) intros x y Hxy. inv Hxy ; constructor ; symmetry; auto.
  (* transitive *) intros x y z Hxy Hyz. 
  inv Hxy; inv Hyz; constructor; etransitivity; eauto. 
Qed.

Hint Extern 1 => 
  match goal with 
    | |- low_equiv_instr _ _ _ => reflexivity
  end.

Inductive low_equiv_list (A: Type) (low_equiv_a: A -> A -> Prop) : 
  list A -> list A -> Prop :=
| le_nil: low_equiv_list low_equiv_a nil nil
| le_cons: forall a1 a2 l1 l2, 
  (low_equiv_a a1 a2) ->
  (low_equiv_list low_equiv_a l1 l2) ->
  low_equiv_list low_equiv_a (a1::l1) (a2::l2). 
Hint Constructors low_equiv_list.

Lemma low_equiv_list_app_left (A: Type) (low_equiv_a: A -> A -> Prop) : 
  forall l1 l1' l2 l2', 
    low_equiv_list low_equiv_a (l1++l2) (l1'++l2') ->
    length l1 = length l1' ->
    low_equiv_list low_equiv_a l1 l1'.
Proof.
  induction l1; intros; simpl in *. 
  destruct l1'; [ eauto | inv H0].
  destruct l1'; [inv H0 | eauto].
  simpl in *; inv H; auto.
  constructor ; eauto.
Qed.

Lemma low_equiv_list_app_right (A: Type) (low_equiv_a: A -> A -> Prop) : 
  forall l1 l1' l2 l2', 
    low_equiv_list low_equiv_a (l1++l2) (l1'++l2') ->
    length l1 = length l1' ->
    low_equiv_list low_equiv_a l2 l2'.
Proof.
  induction l1; intros; simpl in *. 
  destruct l1' ; [simpl in * ; auto | inv H0].
  destruct l1'; [ inv H0 | simpl in * ].
  inv H; auto.
  eapply IHl1 ; eauto.
Qed.

Lemma low_equiv_list_app (A: Type) (R: A -> A -> Prop) : forall l1 l2 l1' l2',
  low_equiv_list R l1 l2 ->
  low_equiv_list R l1' l2' ->
  low_equiv_list R (l1++l1') (l2++l2').
Proof.
  induction l1; intros.
  inv H.  simpl ; auto.
  inv H. simpl. constructor ; auto.
Qed. 

Lemma join_low_equiv_list (f: Z -> Z -> Z): 
  forall o s1 s2 v1 v2 v1' v2' v1l v1'l v2l v2'l,
  low_equiv_list (low_equiv_stkelt o) s1 s2 ->
  low_equiv_atom o (v1, v1l) (v2, v2l) ->
  low_equiv_atom o (v1', v1'l) (v2', v2'l) ->
  low_equiv_list (low_equiv_stkelt o)
  ((AData (f v1 v1', join v1l v1'l)) :: s1)
  ((AData (f v2 v2', join v2l v2'l)) :: s2).
Proof.
  intros. constructor ; auto.
  inv H0; inv H1; constructor; auto with lat.
Qed.
    
Lemma index_list_low_eq (A: Type) (low_equiv: A -> A -> Prop) : 
  forall n l1 l2 v1 v2,
    low_equiv_list low_equiv l1 l2 ->
    index_list n l1 = Some v1 ->
    index_list n l2 = Some v2 ->
    low_equiv v1 v2.
Proof.
  induction n ; intros.
  inv H; (simpl in * ; congruence).
  destruct l1, l2; (simpl in * ; try congruence).
  inv H.
  eapply IHn ; eauto.
Qed.


Lemma index_list_Z_low_eq (A: Type) (low_equiv: A -> A -> Prop) : 
  forall i l1 l2 v1 v2,
    low_equiv_list low_equiv l1 l2 ->
    index_list_Z i l1 = Some v1 ->
    index_list_Z i l2 = Some v2 ->
    low_equiv v1 v2.
Proof.
  intros. eapply index_list_low_eq; eauto. 
  eapply index_list_Z_nat; eauto. 
  eapply index_list_Z_nat; eauto. 
Qed.

Lemma update_list_high: forall o m1 m2,
  low_equiv_list (low_equiv_atom o) m1 m2 ->
  forall a m1' o1 v l1 l2
    (Hl1 : l1 <: o = false)
    (Hl2 : l2 <: o = false), 
    index_list a m1 = Some (o1, l1) ->
    update_list a (v, l2) m1 = Some m1' ->
    low_equiv_list (low_equiv_atom o) m1' m2.
Proof.
  induction 1; intros.
  destruct a; simpl in *; allinv.
  
  destruct a; simpl in *; allinv.
  constructor ; auto. inv H ; auto.

  case_eq (update_list a (v, l3) l1) ; intros;
  rewrite H3 in *; allinv.
  constructor; auto.
  eapply (IHlow_equiv_list a l o1 v l0) ; eauto.
Qed.  

Lemma update_list_Z_high: forall o m1 m2,
  low_equiv_list (low_equiv_atom o) m1 m2 ->
  forall a m1' o1 v l1 l2
    (Hl1 : l1 <: o = false)
    (Hl2 : l2 <: o = false), 
    index_list_Z a m1 = Some (o1, l1) ->
    update_list_Z a (v, l2) m1 = Some m1' ->
    low_equiv_list (low_equiv_atom o) m1' m2.
Proof.
  intros. 
  eapply update_list_high with (l1 := l1) (l2 := l2); eauto. 
  eapply index_list_Z_nat; eauto. 
  eapply update_list_Z_nat; eauto.
Qed.


Global Instance low_list 
          (A: Type) 
          (R: relation A)
          (EqR: Equivalence R) : @Equivalence (list A) (@low_equiv_list A R).
Proof.
  constructor.
  (* reflexive *) unfold Reflexive. induction x; intros; constructor; auto. reflexivity.
  (* symmetric *) 
  unfold Symmetric. 
  induction x ; intros; (inv H ; constructor ; auto). symmetry; auto.
  (* transitive *) 
  unfold Transitive. 
  induction x; intros. 
  inv H. auto. inv H. inv H0.
  constructor. etransitivity; eauto. 
  eapply IHx ; eauto.
Qed.

Hint Extern 1 => 
  match goal with 
    | |- low_equiv_list _ _ _ => reflexivity
  end.

Lemma update_list_low_equiv: forall a obs l  m m' o v
  (Hl : l <: obs = false),
  index_list a m = Some (o, l) ->
  update_list a (v, l) m = Some m' ->
  low_equiv_list (low_equiv_atom obs) m m'.
Proof.
  induction a; intros.
  destruct m ; simpl in *; allinv. 
  constructor; auto. 
  
  destruct m ; simpl in *; allinv. 
  case_eq (update_list a (v, l) m) ; intros; rewrite H1 in *; allinv.
  constructor; eauto.
Qed.  

Lemma update_list_Z_low_equiv: forall a obs l  m m' o v
  (Hl : l <: obs = false),
  index_list_Z a m = Some (o, l) ->
  update_list_Z a (v, l) m = Some m' ->
  low_equiv_list (low_equiv_atom obs) m m'.
Proof.
  intros. eapply update_list_low_equiv; eauto. 
  eapply index_list_Z_nat; eauto. 
  eapply update_list_Z_nat; eauto.
Qed.

Lemma update_list_low : forall o n m1 m2 a1 a2 m1' m2',
  low_equiv_list (low_equiv_atom o) m1 m2 ->
  low_equiv_atom o a1 a2 ->
  update_list n a1 m1 = Some m1' ->
  update_list n a2 m2 = Some m2' ->
  low_equiv_list (low_equiv_atom o) m1' m2'.
Proof.
  induction n ; intros.
  inv H; simpl in *; allinv.
  constructor ; auto.
  
  inv H.
  simpl in *; allinv.
  simpl in H2, H1.
  case_eq (update_list n a2 l2) ; case_eq (update_list n a1 l1) ; intros; 
    rewrite H in * ; rewrite H5 in * ; allinv.
  constructor ; eauto.
Qed.

Lemma update_list_Z_low : forall o n m1 m2 a1 a2 m1' m2',
  low_equiv_list (low_equiv_atom o) m1 m2 ->
  low_equiv_atom o a1 a2 ->
  update_list_Z n a1 m1 = Some m1' ->
  update_list_Z n a2 m2 = Some m2' ->
  low_equiv_list (low_equiv_atom o) m1' m2'.
Proof.
  intros. eapply update_list_low; eauto.
  eapply update_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto. 
Qed.

Lemma low_equiv_list_update_Z: forall o a1 a2 a1l a2l o1 o1l o2 o2l m1 m2 m1' m2' v1 v1l v2 v2l,
    low_equiv_atom o (a1, a1l) (a2, a2l) ->
    low_equiv_list (low_equiv_atom o) m1 m2 ->
    index_list_Z a1 m1 = Some (o1, o1l) ->
    index_list_Z a2 m2 = Some (o2, o2l) ->
     a1l <: o1l = true ->
     a2l <: o2l = true ->  
    low_equiv_atom o (v1, v1l) (v2, v2l) ->
    update_list_Z a1 (v1, join a1l v1l) m1 = Some m1' ->
    update_list_Z a2 (v2, join a2l v2l) m2 = Some m2' ->
    low_equiv_list (low_equiv_atom o) m1' m2'.
Proof.
  intros.
  inv H; inv H5. 

  eapply (@update_list_Z_low o) ; eauto. 
  
  eapply update_list_Z_low with (3:= H6) (4:= H7) ; eauto.
  econstructor 2; eauto with lat.

  assert (low_equiv_list (low_equiv_atom o) m1' m1).
  assert (a1l \_/ v2l <: o = false) by eauto with lat. 
  eapply update_list_Z_high with (4:= H1); eauto.  
  destruct (flows_dec o1l o); auto.
  assert (flows a1l o = true); eauto with lat. 
  
  assert (low_equiv_list (low_equiv_atom o) m1' m2) by (etransitivity; eauto). 
  assert (a2l \_/ v2l <: o = false) by eauto with lat.
  exploit (@update_list_Z_spec Atom (v2, a1l \_/ v2l)) ; eauto. intros HH.
  assert (low_equiv_list (low_equiv_atom o) m2' m2).
  eapply update_list_Z_high with (4:= H2); eauto. 
  destruct (flows_dec o2l o); auto.
  assert (flows a2l o = true); eauto with lat.
  etransitivity; eauto. symmetry; auto. 

  assert (a1l \_/ v1l <: o = false) by eauto with lat. 
  assert (low_equiv_list (low_equiv_atom o) m1' m1).
  eapply update_list_Z_high with (4:= H1); eauto. 
  destruct (flows_dec o1l o); auto.
  assert (flows a1l o = true); eauto with lat.  
  
  exploit (@update_list_Z_spec Atom (v1, a1l \_/ v1l)) ; eauto. intros HH.
  assert (low_equiv_list (low_equiv_atom o) m1' m2). 
  etransitivity ; eauto. 

  assert (a2l \_/ v2l <: o = false) by eauto with lat.
  assert (low_equiv_list (low_equiv_atom o) m2' m2).
  eapply update_list_Z_high with (4:= H2); eauto. 
  destruct (flows_dec o2l o); auto.
  assert (flows a2l o = true); eauto with lat.
  etransitivity; eauto. symmetry; eauto. 
Qed.

Lemma update_high_low_equiv: forall o addr m v l l' v' m',
  index_list addr m = Some (v,l) ->
  l <: o = false ->
  l <: l' = true ->
  update_list addr (v',l') m = Some m' ->
  low_equiv_list (low_equiv_atom o) m m'.
Proof.
  induction addr; intros.
  destruct m ; simpl in *; allinv.
  constructor ; eauto.
  constructor 2; auto with lat. 
  destruct (flows_dec l' o); auto.
  assert (flows l o = true); eauto with lat.  
  
  destruct m ; simpl in *; allinv.
  remember (update_list addr (v', l') m) as up.
  destruct up; allinv.
  constructor; eauto.
Qed.  
  
Lemma update_Z_high_low_equiv: forall o addr m v l l' v' m',
  index_list_Z addr m = Some (v,l) ->
  l <: o = false ->
  l <: l' = true ->
  update_list_Z addr (v',l') m = Some m' ->
  low_equiv_list (low_equiv_atom o) m m'.
Proof.
  intros. eapply update_high_low_equiv; eauto. 
  eapply index_list_Z_nat; eauto. 
  eapply update_list_Z_nat; eauto.
Qed.


Lemma index_list_Z_low_eq_instr : 
  forall o i1 i2 pcv v1 v2,
    low_equiv_list (low_equiv_instr o) i1 i2 ->
    index_list_Z pcv i1 = Some v1 ->
    index_list_Z pcv i2 = Some v2 ->
    low_equiv_instr o v1 v2.
Proof.
  intros.
  case_eq (index_list_Z pcv i1) ; case_eq (index_list_Z pcv i2) ; intros;
  rewrite H2 in * ; rewrite H3 in *; allinv.
  eapply index_list_Z_low_eq ; eauto.
Qed.  


Fixpoint below_lret (o: Label) (stk: list (@StkElmt Label)) : list StkElmt :=
  match stk with
    | nil => nil 
    | (ARet (_,l) _)::stk' => 
      match flows l o with 
        | true => stk
        | false => below_lret o stk'
      end
    | _::stk' => below_lret o stk'
  end.

Lemma below_lret_low_equiv : forall o l1 l2, 
  low_equiv_list (low_equiv_stkelt o) l1 l2 ->
  low_equiv_list (low_equiv_stkelt o) (below_lret o l1) (below_lret o l2). 
Proof.
  induction 1; intros.
  simpl ; auto.
  inv H; (simpl; auto). 
  inv LEa; (rewrite H in *; auto).
  rewrite H1 ; auto.
Qed.

Lemma below_lret_adata : forall o l l', 
  (forall d, In d l -> exists a : Atom, d = AData a) ->
  below_lret o (l ++ l') = below_lret o l'.
Proof.
  induction l; intros.
  simpl; auto.
  destruct a. simpl ; auto. eapply IHl ; eauto.
  intros. eapply H ; eauto. constructor 2 ; auto.
  
  eelim (H (ARet a b)); intros.
  congruence. 
  constructor ; auto.
Qed.

Inductive low_equiv_full_state (o: Label) : @AS Label -> @AS Label -> Prop := 
| low_equiv_high: 
  forall l1 l2 m1 m2 i1 i2 stk1 stk2 pcv1 pcv2
    (Flowl1: l1 <: o = false)
    (Flowl2: l2 <: o = false)
    (LEm : low_equiv_list (low_equiv_atom o) m1 m2)
    (LEi : low_equiv_list (low_equiv_instr o) i1 i2)
    (LEsH : low_equiv_list (low_equiv_stkelt o) (below_lret o stk1) (below_lret o stk2)),
    low_equiv_full_state o
      (AState m1 i1 stk1 (pcv1,l1))
      (AState m2 i2 stk2 (pcv2,l2))
| low_equiv_low:
  forall l m1 m2 i1 i2 stk1 stk2 pcv
    (Flowl: l <: o = true)
    (LEm : low_equiv_list (low_equiv_atom o) m1 m2)
    (LEi : low_equiv_list (low_equiv_instr o) i1 i2)
    (LEs : low_equiv_list (low_equiv_stkelt o) stk1 stk2),
    low_equiv_full_state o
      (AState m1 i1 stk1 (pcv,l))
      (AState m2 i2 stk2 (pcv,l)).
Hint Constructors low_equiv_full_state.

Global Instance low_state (o: Label) : @Equivalence AS (@low_equiv_full_state o).
Proof.
  constructor.
  (* reflexive *) intros x. destruct x. destruct apc. 
  destruct (flows_dec l o).
  constructor 2 ; eauto. 
  constructor ; eauto. 
  (* symmetry *) 
  intros s s' Hss'.  inv Hss'. 
  (constructor; eauto); symmetry ; eauto. 
  (constructor 2; eauto) ; symmetry; eauto.  
  (* transitive *)
  intros s s' s'' Hss' Hs's''.
  inv Hss' ; inv Hs's''. 
  (constructor ; eauto); etransitivity; eauto. 
  (constructor ; eauto); etransitivity; eauto. 
  apply below_lret_low_equiv; auto.
  (constructor ; eauto); etransitivity; eauto. 
  apply below_lret_low_equiv in LEs; auto.
  etransitivity; eauto.
  (constructor 2 ; eauto); etransitivity; eauto.   
Qed.

Hint Extern 1 => 
  match goal with 
    | |- low_equiv_full_state _ _ _ => reflexivity
  end.

Lemma pc_labels1 : forall o s1 s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s1 -> 
  low_pc o s2.
Proof.
  induction 1; intros. unfold low_pc in *;  simpl in *.
  inv H. congruence.
  unfold low_pc in *;  simpl in *. auto.
Qed.

Lemma pc_labels2 : forall o s1 s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s2 ->
  low_pc o s1.
Proof.
  induction 1; intros. unfold low_pc in *;  simpl in *.
  inv H. congruence.
  unfold low_pc in *;  simpl in *. auto.
Qed.

Lemma index_list_low_equiv_some: forall (A: Type) (R: relation A) n e l l', 
  low_equiv_list R l l' ->
  index_list n l = None ->
  index_list n l' = Some e ->
  False.
Proof.
  induction n ; intros.
  destruct l' ; inv H ; simpl in *; try congruence.
  destruct l' ; inv H ; simpl in * ; try congruence.
  eapply IHn ; eauto.
Qed.

Lemma index_list_Z_low_equiv_some: forall (A: Type) (R: relation A) n e l l', 
  low_equiv_list R l l' ->
  index_list_Z n l = None ->
  index_list_Z n l' = Some e ->
  False.
Proof.
  unfold index_list_Z. intros. 
  destruct (n <? 0)%Z. congruence.
  eapply index_list_low_equiv_some; eauto.
Qed.

Lemma low_equiv_low_success : forall o s1 s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s2 ->
  success s2 ->
  success s1.
Proof.
  intros. inv H; (unfold low_pc in H0; inv H0).
  break_success. simpl in *.
  remember (index_list_Z pcv1 i1) as oinstr'.  
  congruence. 
  
  break_success. simpl in *.
  remember (index_list_Z pcv i1) as oinstr'.  
  destruct oinstr'; symmetry in Heqoinstr'.
  exploit index_list_Z_low_eq_instr; eauto. intros Hhalt. 
  inv Hhalt; auto.
  eapply index_list_Z_low_equiv_some with (1:= LEi); eauto.
Qed.

End ObsEquiv.

Hint Resolve low_state.

Hint Constructors 
  low_equiv_atom
  low_equiv_stkelt
  low_equiv_list
  low_equiv_instr
  low_equiv_full_state.

Hint Extern 1 => 
  match goal with 
    | |- low_equiv_atom _ _ _ => reflexivity
    | |- low_equiv_stkelt _ _ _ => reflexivity
    | |- low_equiv_list _ _ _ => reflexivity
    | |- low_equiv_instr _ _ _ => reflexivity
    | |- low_equiv_full_state _ _ _ => reflexivity
  end.


(* Lemmas on the executable machine. Keep it for now. Will have to
   move them away in another file at some point *)

(* Lemma low_equiv_drop: forall o m1 m2 i1 i2 pc1 pc2 stk1 stk2 rstk1 rstk2 reta1 reta2, *)
(*   low_equiv_list (low_equiv_stkelt o) stk1 stk2 -> *)
(*   drop_data (length stk1) (AState m1 i1 stk1 pc1) = Some ((AState m1 i1 rstk1 pc1), reta1) -> *)
(*   drop_data (length stk2) (AState m2 i2 stk2 pc2) = Some ((AState m2 i2 rstk2 pc2), reta2) -> *)
(*   (low_equiv_stkelt o reta1 reta2 *)
(*   /\ low_equiv_list (low_equiv_stkelt o) rstk1 rstk2). *)
(* Proof. *)
(*   induction 1 ; intros. *)
(*   simpl in *; allinv. *)
  
(*   simpl in *. destruct a1, a2; try solve [inv H ]. *)
  
(*   Case "AData". *)
(*   step_in @pop_astk. *)
(*   step_in @get_astk. *)
(*   step_in get. *)
(*   step_in @set_astk. *)
(*   step_in get. *)
(*   step_in put. *)
(*   unfold upd_astk in *. simpl in *. *)
(*   eapply IHlow_equiv_list; eauto. *)
  
(*   Case "ARet". *)
(*   step_in @pop_astk. *)
(*   step_in @get_astk. *)
(*   step_in get. allinv. *)
(*   step_in @set_astk. *)
(*   step_in get. *)
(*   step_in put. auto. *)
(* Qed. *)


(* Lemma index_aimem_low_eq_instr :  *)
(*   forall o m1 m2 i1 i2 stk1 stk2 pc1 pc2 pcv s1 s2 v1 v2, *)
(*     low_equiv_list (low_equiv_instr o) i1 i2 -> *)
(*     index_aimem pcv (AState m1 i1 stk1 pc1) = Some (s1, v1) -> *)
(*     index_aimem pcv (AState m2 i2 stk2 pc2) = Some (s2, v2) -> *)
(*     low_equiv_instr o v1 v2. *)
(* Proof. *)
(*   intros. *)
(*   step_in @index_aimem. *)
(*   step_in @get_aimem. *)
(*   step_in get. *)
(*   simpl in *. *)
(*   case_eq (index_list_Z pcv i1) ; case_eq (index_list_Z pcv i2) ; intros; *)
(*   rewrite H2 in * ; rewrite H3 in *; allinv. *)
(*   eapply index_list_Z_low_eq ; eauto. *)
(* Qed.   *)

(* Lemma index_amem_low_eq_atom :  *)
(*   forall o m1 m2 i1 i2 stk1 stk2 pc1 pc2 a s1 s2 v1 v2, *)
(*   low_equiv_list (low_equiv_atom o) m1 m2 -> *)
(*   index_amem a (AState m1 i1 stk1 pc1) = Some (s1, v1) -> *)
(*   index_amem a (AState m2 i2 stk2 pc2) = Some (s2, v2) -> *)
(*   low_equiv_atom o v1 v2. *)
(* Proof. *)
(*   intros. *)
(*   step_in @index_amem. *)
(*   step_in @get_amem. *)
(*   step_in get. *)
(*   simpl in *. *)
(*   case_eq (index_list_Z a m1) ; case_eq (index_list_Z a m2) ; intros; *)
(*   rewrite H2 in * ; rewrite H3 in *; allinv. *)
(*   eapply index_list_Z_low_eq ; eauto. *)
(* Qed.   *)
