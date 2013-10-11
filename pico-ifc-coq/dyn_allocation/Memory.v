Require Import Datatypes.
Require Import Lattices.
Require Import ZArith.
Require Import List.
Require Import EquivDec.

Fixpoint replicate {A:Type} (n:nat) (a:A) : list A :=
  match n with
    | O => nil
    | S n' => a :: replicate n' a
  end.

Definition zreplicate {A:Type} (n:Z) (a:A) : option (list A) :=
  if Z_lt_dec n 0 then None
  else Some (replicate (Z.to_nat n) a).

Lemma index_list_replicate: forall A n (a:A) n',
  index_list n' (replicate n a) = if lt_dec n' n then Some a else None.
Proof.
  induction n; destruct n'; simpl; try congruence.
  rewrite IHn.
  do 2 destruct lt_dec; try congruence; try omega.
Qed.

Lemma index_list_Z_zreplicate: forall A z (a:A) z' l,
  zreplicate z a = Some l ->
  index_list_Z z' l = if Z_le_dec 0 z' then
                        if Z_lt_dec z' z then Some a else None else None.
Proof.
  unfold zreplicate, index_list_Z; intros.
  destruct (Z_lt_dec z 0); try congruence.
  inv H.
  destruct (z' <? 0)%Z eqn:Ez.
  - rewrite Z.ltb_lt in Ez.
    destruct Z_lt_dec; try omega.
    destruct Z_le_dec; auto; omega.
  - assert (~ (z' < 0 )%Z).
    rewrite <- Z.ltb_lt; try congruence.
    destruct Z_le_dec; try omega.
    rewrite index_list_replicate.
    assert ( (z'<z)%Z <-> (Z.to_nat z') < (Z.to_nat z)).
      apply Z2Nat.inj_lt; try omega.
    destruct lt_dec; destruct Z_lt_dec; auto; try omega.
Qed.

Inductive alloc_mode := Global | Local.

Module Type MEM.
  (* Type of memory is parameterized by the type of stamps and the type of block *)
  Parameter t : Type -> Type -> Type.

  Parameter block : Type -> Type.
  Declare Instance EqDec_block : forall {S} {_:EqDec S eq}, EqDec (block S) eq.
  Parameter stamp : forall {S}, block S -> S.

  (* DD -> DP : is a block some kind of "stamped pointer"? *)
  Parameter get_frame : forall {A S}, t A S -> block S -> option (list A).  
  Parameter upd_frame : 
    forall {A S:Type} {EqS:EqDec S eq}, t A S -> block S -> list A -> option (t A S).
  Parameter upd_get_frame : forall A S (EqS:EqDec S eq) (m:t A S) (b:block S) fr fr',
    get_frame m b = Some fr ->
    exists m',
      upd_frame m b fr' = Some m'.
  Parameter get_upd_frame : forall A S (EqS:EqDec S eq) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    forall b', 
      get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Parameter upd_frame_defined : forall A S (EqS:EqDec S eq) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    exists fr', get_frame m b = Some fr'.

  Parameter empty : forall A S, t A S.
  Parameter get_empty : forall A S (b:block S), get_frame (empty A S) b = None.

  (* Create a memory with some block initialized to a frame *)
  Parameter init : forall A S {eqS:EqDec S eq},
                     alloc_mode ->
                     block S ->
                     list A ->
                     t A S.

  Parameter get_init_eq : forall A S {eqS:EqDec S eq}
                                 mode (b : block S) (f : list A),
                            get_frame (init A S mode b f) b = Some f.

  Parameter get_init_neq : forall A S {eqS:EqDec S eq}
                                  mode (b b' : block S) (f : list A),
                             b' <> b ->
                             get_frame (init A S mode b f) b' = None.

  Parameter alloc :
    forall {A S} {EqS:EqDec S eq}, alloc_mode -> t A S -> S -> list A -> (block S * t A S).
  Parameter alloc_stamp : forall A S (EqS:EqDec S eq) am (m m':t A S) s fr b, 
    alloc am m s fr = (b,m') -> stamp b = s.
  Parameter alloc_get_fresh : forall A S (EqS:EqDec S eq) am (m m':t A S) s fr b, 
    alloc am m s fr = (b,m') -> get_frame m b = None.
  Parameter alloc_get_frame : forall A S (eqS:EqDec S eq) am (m m':t A S) s fr b, 
    alloc am m s fr = (b,m') ->
    forall b', get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Parameter alloc_upd : forall A S (eqS:EqDec S eq) am (m:t A S) b fr1 s fr2 m',
    upd_frame m b fr1 = Some m' ->
    fst (alloc am m' s fr2) = fst (alloc am m s fr2).
  Parameter alloc_local_comm : 
    forall A S (EqS:EqDec S eq)  (m m1 m2 m1' m2':t A S) s s' fr fr' b1 b2 b1', 
    s <> s' ->                                           
    alloc Local m s fr = (b1,m1) -> 
    alloc Local m1 s' fr' = (b2,m2) -> 
    alloc Local m s' fr' = (b1',m1') ->
    b1' = b2.
  Parameter alloc2_local : 
    forall A S (EqS:EqDec S eq)  (m1 m2 m1' m2':t A S) s fr1 fr2 fr' b, 
    alloc Local m1 s fr1 = (b,m1') -> 
    alloc Local m2 s fr2 = (b,m2') ->
    fst (alloc Local m1' s fr') = fst (alloc Local m2' s fr').

  Parameter alloc_next_block_no_fr : 
    forall A S (EqS:EqDec S eq) (m:t A S) s fr1 fr2,
    fst (alloc Local m s fr1) = fst (alloc Local m s fr2).

  Parameter map : forall {A B S}, (list A-> list B) -> t A S -> t B S.
  Parameter map_spec : forall A B S (f:list A-> list B) (m:t A S),
    forall b, get_frame (map f m) b = option_map f (get_frame m b).

End MEM.

Module Mem: MEM.
  Definition block S := (Z * S)%type.

  Instance EqDec_block : forall {S} {EqS:EqDec S eq}, EqDec (block S) eq.
  Proof.
    intros S E (x,s) (x',s').
    destruct (Z.eq_dec x x').
    destruct (s == s').
    left; congruence.
    right; congruence.
    right; congruence.
  Qed.

  Definition stamp S : block S -> S := snd.

  Record _t {A S} := MEM {
     content :> block S -> option (list A);
     next : S -> Z;
     content_next : forall s i, (next s<=i)%Z -> content (i,s) = None
  }.
  Implicit Arguments _t [].
  Implicit Arguments MEM [A S].
  Definition t := _t.

  Definition get_frame {A S} (m:t A S) := content m.

  Program Definition map {A B S} (f:list A-> list B) (m:t A S) : t B S := 
    MEM 
      (fun b => option_map f (get_frame m b))
      (next m)
      _.
  Next Obligation.
    simpl; rewrite content_next; auto.
  Qed.

  Lemma map_spec : forall A B S (f:list A-> list B) (m:t A S),
    forall b, get_frame (map f m) b = option_map f (get_frame m b).
  Proof.
    auto.
  Qed.

  Program Definition empty A S : t A S := MEM 
    (fun b => None) (fun _ => 1%Z) _.

  Lemma get_empty : forall A S b, get_frame (empty A S) b = None.
  Proof. auto. Qed.

  Program Definition init A S {eqS : EqDec S eq} (am : alloc_mode) b f : t A S := MEM
    (fun b' : block S => if b' == b then Some f else None)
    (fun s => if s == stamp _ b then fst b + 1 else 1)%Z
    _.
  Next Obligation.
    simpl in *.
    destruct (s == s0) as [EQ | NEQ].
    - compute in EQ. subst s0.
      destruct (equiv_dec (i,s)) as [contra|]; trivial.
      inv contra.
      omega.
    - destruct (equiv_dec (i,s)) as [E|E]; try congruence.
  Qed.

  Lemma get_init_eq : forall A S {eqS:EqDec S eq}
                             mode (b : block S) (f : list A),
                        get_frame (init A S mode b f) b = Some f.
  Proof.
    unfold init. simpl.
    intros.
    match goal with
      | |- context [if ?b then _ else _] =>
        destruct b; congruence
    end.
  Qed.

  Lemma get_init_neq : forall A S {eqS:EqDec S eq}
                              mode (b b' : block S) (f : list A),
                         b' <> b ->
                         get_frame (init A S mode b f) b' = None.
  Proof.
    unfold init. simpl.
    intros.
    match goal with
      | |- context [if ?b then _ else _] =>
        destruct b; congruence
    end.
  Qed.

  Program Definition upd_frame_rich {A S} {EqS:EqDec S eq} (m:t A S) (b0:block S) (fr:list A)
  : option { m' : (t A S) |
             (forall b', 
                get_frame m' b' = if b0 == b' then Some fr else get_frame m b') 
           /\ forall s, next m s = next m' s} :=
    match m b0 with
      | None => None
      | Some _ =>
        Some (MEM
                (fun b => if b0 == b then Some fr else m b) 
                (next m) _)
    end.
  Next Obligation.
    destruct (equiv_dec b0).
    - destruct b0; inv e.
      rewrite content_next in Heq_anonymous; congruence.
    - apply content_next; auto.
  Qed.

  Definition upd_frame {A S} {EqS:EqDec S eq} (m:t A S) (b0:block S) (fr:list A)
  : option (t A S) := 
    match upd_frame_rich m b0 fr with
      | None => None
      | Some (exist m' _) => Some m'
    end.

  Lemma upd_get_frame : forall A S (EqS:EqDec S eq) (m:t A S) (b:block S) fr fr',
    get_frame m b = Some fr ->
    exists m',
      upd_frame m b fr' = Some m'.
  Proof.
    (* Sad.... *)
    unfold upd_frame, upd_frame_rich, get_frame.
    intros.
    generalize (@eq_refl (option (list A)) (m b)).
    generalize (upd_frame_rich_obligation_2 A S EqS m b fr').
    simpl.
    generalize (upd_frame_rich_obligation_1 A S EqS m b fr').
    rewrite H.
    simpl.
    intros H1 H2 H3.
    eauto.
  Qed.

  Lemma get_upd_frame : forall A S (eqS:EqDec S eq) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    forall b', 
      get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Proof.
    unfold upd_frame; intros.
    destruct (upd_frame_rich m b fr); try congruence.
    destruct s; inv H; intuition.    
  Qed.

  Lemma upd_frame_defined : forall A S (EqS:EqDec S eq) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    exists fr', get_frame m b = Some fr'.
  Proof.
    unfold upd_frame, upd_frame_rich, get_frame.
    intros until 0.
    generalize (@eq_refl (option (list A)) (@content A S m b)).
    generalize (upd_frame_rich_obligation_2 A S EqS m b fr).
    simpl.
    generalize (upd_frame_rich_obligation_1 A S EqS m b fr).
    simpl.
    intros.
    destruct (m b); eauto; congruence.
  Qed.

  Opaque Z.add.

  Program Definition alloc
             {A S} {EqS:EqDec S eq} (am:alloc_mode) (m:t A S) (s:S) (fr:list A) 
            : (block S * t A S) :=
    ((next m s,s),
     MEM
       (fun b' => if (next m s,s) == b' then Some fr else get_frame m b')
       (fun s' => if s == s' then (1 + next m s)%Z else next m s')
       _).
  Next Obligation.
    destruct (equiv_dec (next m s, s)).
    - inv e.
      destruct (equiv_dec s0); try congruence.
      omega.
    - destruct (equiv_dec s).
      + inv e.
        apply content_next; omega.
      + apply content_next; omega.
  Qed.

  Lemma alloc_stamp : forall A S (EqS:EqDec S eq) am (m m':t A S) s fr b, 
    alloc am m s fr = (b,m') -> stamp _ b = s.
  Proof.
    unfold alloc; intros.
    inv H; auto.
  Qed.

  Lemma alloc_get_fresh : forall A S (EqS:EqDec S eq) am (m m':t A S) s fr b, 
    alloc am m s fr = (b,m') -> get_frame m b = None.
  Proof.
    unfold alloc; intros.
    inv H.
    apply content_next; omega.
  Qed.

  Lemma alloc_get_frame : forall A S (eqS:EqDec S eq) am (m m':t A S) s fr b, 
    alloc am m s fr = (b,m') ->
    forall b', get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Proof.
    unfold alloc; intros.
    inv H; auto.
  Qed.

  Lemma alloc_upd : forall A S (eqS:EqDec S eq) am (m:t A S) b fr1 s fr2 m',
    upd_frame m b fr1 = Some m' ->
    fst (alloc am m' s fr2) = fst (alloc am m s fr2).
  Proof.
    intros A S eqS am m b fr1 s fr2 m' H.
    unfold alloc, upd_frame in *; simpl.
    destruct (upd_frame_rich m b fr1); try congruence.
    destruct s0; inv H.
    destruct a as [_ T].
    rewrite T; auto.
  Qed.

  Lemma alloc_local_comm : 
    forall A S (EqS:EqDec S eq) (m m1 m2 m1' m2':t A S) s s' fr fr' b1 b2 b1', 
    s <> s' ->                                           
    alloc Local m s fr = (b1,m1) -> 
    alloc Local m1 s' fr' = (b2,m2) -> 
    alloc Local m s' fr' = (b1',m1') ->
    b1' = b2.
  Proof.
    intros A S EqS m m1 m2 m1' m2' s s' fr fr' b1 b2 b1' H H0 H1 H2.
    inv H0; inv H1; inv H2.
    destruct (equiv_dec s s'); try congruence.
  Qed.

  Lemma alloc2_local : 
    forall A S (EqS:EqDec S eq)  (m1 m2 m1' m2':t A S) s fr1 fr2 fr' b, 
    alloc Local m1 s fr1 = (b,m1') -> 
    alloc Local m2 s fr2 = (b,m2') ->
    fst (alloc Local m1' s fr') = fst (alloc Local m2' s fr').
  Proof.
    intros A S EqS m1 m2 m1' m2' s fr1 fr2 fr' b H H0.
    inv H; inv H0; simpl.
    rewrite H1; auto.
  Qed.

  Lemma alloc_next_block_no_fr : 
    forall A S (EqS:EqDec S eq) (m:t A S) s fr1 fr2,
    fst (alloc Local m s fr1) = fst (alloc Local m s fr2).
  Proof.
    intros A S EqS m s fr1 fr2.
    unfold alloc; simpl; auto.
  Qed.

End Mem.

(* CH: some of the stuff that follows doesn't really belong in this file *)

Inductive val {S} := 
  | Vint (n:Z)
  | Vptr (b:Mem.block S) (n:Z).
Implicit Arguments val [].

Definition add {S} (v1 v2:val S) : option (val S) :=
  match v1, v2 with
    | Vint i1, Vint i2 => Some (Vint (i1+i2))
    | Vptr b i1, Vint i2 => Some (Vptr b (i1-i2))
    | Vint i1, Vptr b i2 => Some (Vptr b (i1+i2))
    | _, _ => None 
  end.

Definition sub {S} {EqS:EqDec S eq} (v1 v2:val S) : option (val S) :=
  match v1, v2 with
    | Vint i1, Vint i2 => Some (Vint (i1-i2))
    | Vptr b i1, Vint i2 => Some (Vptr b (i1-i2))
    | Vptr b1 i1, Vptr b2 i2 =>
      (* CH: returning the offset difference as an integer would be much
             more natural and useful than returning another pointer *)
      if b1 == b2 then Some (Vptr b1 (i1-i2)) else None
    | _, _ => None 
  end.

Instance EqDec_block : forall {S} {EqS:EqDec S eq}, EqDec (val S) eq.
Proof.
  intros S H [z1|b1 off1] [z2|b2 off2];
  unfold complement, equiv; simpl;
  try solve [right; congruence].
  - destruct (Z.eq_dec z1 z2); subst; auto.
    right. congruence.
  - destruct (b1 == b2) as [Eb | Eb]; subst.
    2: right; congruence.
    compute in Eb. subst.
    destruct (Z.eq_dec off1 off2); subst; auto.
    right; congruence.
Qed.

Definition val_eq {S} {eqS:EqDec S eq} (v1 v2 : val S) : val S :=
  Vint (if v1 == v2 then 1 else 0).

Definition Atom Label S := (val S * Label)%type.
Definition PcAtom Label := (Z * Label)%type.

Definition memory T S :=  Mem.t (Atom T S) S.
Definition block S := Mem.block S.

Definition load {A S} (b:block S) (addr:Z) (m:memory A S) : option (Atom A S) :=
  match Mem.get_frame m b with
    | None => None
    | Some fr => index_list_Z addr fr
  end.

Definition store {A S} {EqS:EqDec S eq} (b:block S) (addr:Z) (a:Atom A S) (m:memory A S) 
: option (memory A S) :=
  match Mem.get_frame m b with
    | None => None
    | Some fr => 
      match update_list_Z addr a fr with
        | None => None
        | Some fr' => (Mem.upd_frame m b fr')
      end
  end.

(* [alloc s size a m] returns : 
 - a block stamped [s], pointing to a new block of size [size], initialized with all [a]
 - the new memory where that block has been allocated
*)
Definition alloc {A S} {EqS:EqDec S eq} (am:alloc_mode)
           (s:S) (size:Z) (a:Atom A S) (m:memory A S): option (block S * memory A S) :=
  match zreplicate size a with
    | Some fr => Some (Mem.alloc am m s fr)
    | None => None
  end.

Lemma load_alloc : forall {A S} {eqS:EqDec S eq} {am} {m m':memory A S} {size s a b}, 
    alloc am s size a m = Some (b,m') ->
    forall b' ofs', 
      load b' ofs' m' =
      if b == b' then if Z_le_dec 0 ofs' then
                        if Z_lt_dec ofs' size then Some a else None
                      else None
      else load b' ofs' m.
Proof.
  unfold alloc, load; intros.
  destruct (zreplicate size a) eqn:Ez; try congruence; inv H.
  rewrite (Mem.alloc_get_frame _ _ _ _ _ _ _ _ _ H1).
  destruct (equiv_dec b).
  - inv e.
    destruct (equiv_dec b'); try congruence.
    eapply index_list_Z_zreplicate; eauto.
  - destruct (equiv_dec b); try congruence.
Qed.

Lemma load_store : forall {A S} {eqS:EqDec S eq} {m m':memory A S} {b ofs a}, 
    store b ofs a m = Some m' ->
    forall b' ofs', 
      load b' ofs' m' =
      if b == b' then
        if Z_eq_dec ofs ofs' then Some a else load b' ofs' m
      else load b' ofs' m.
Proof.
  unfold store, load; intros.
  destruct (Mem.get_frame m b) eqn:E1; try congruence.
  destruct (update_list_Z ofs a l) eqn:E2; try congruence.
  rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H).
  destruct (equiv_dec b);
  destruct (equiv_dec b); try congruence.
  - inv e; clear e0.
    destruct Z.eq_dec.
    + inv e.
      eapply update_list_Z_spec; eauto.
    + rewrite E1.
      symmetry.
      eapply update_list_Z_spec2; eauto.
Qed.

Lemma load_store_old : forall {A S} {eqS:EqDec S eq} {m m':memory A S} {b ofs a}, 
    store b ofs a m = Some m' ->
    forall b' ofs', 
      (b',ofs') <> (b,ofs) ->
      load b' ofs' m' = load b' ofs' m.
Proof.
  intros.
  rewrite (load_store H).
  destruct (@equiv_dec (block S)); try congruence.
  destruct Z.eq_dec; try congruence.
Qed.

Lemma load_store_new : forall {A S} {eqS:EqDec S eq} {m m':memory A S} {b ofs a}, 
    store b ofs a m = Some m' ->
    load b ofs m' = Some a.
Proof.
  intros.
  rewrite (load_store H).
  destruct (@equiv_dec (block S)); try congruence.
  destruct Z.eq_dec; try congruence.
Qed.

Lemma load_some_store_some : forall {A S} {eqS:EqDec S eq} {m:memory A S} {b ofs a}, 
    load b ofs m = Some a ->
    forall a':Atom A S,
      exists m', store b ofs a' m = Some m'.
Proof.
  unfold load, store; intros.
  destruct (Mem.get_frame m b) eqn:E; try congruence.
  exploit index_list_Z_valid; eauto.
  destruct 1.                                
  destruct (@update_list_Z_Some _ a' l ofs); auto.
  rewrite H2.
  eapply Mem.upd_get_frame; eauto.
Qed.

Lemma alloc_get_frame_old :
  forall T S {eqS : EqDec S eq} mode mem (stamp : S) (frame frame' : list T) b b' mem'
         (ALLOC : Mem.alloc mode mem stamp frame' = (b', mem'))
         (FRAME : Mem.get_frame mem b = Some frame),
    Mem.get_frame mem' b = Some frame.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b' == b) as [E | E]; auto.
  compute in E. subst b'.
  exploit Mem.alloc_get_fresh; eauto.
  congruence.
Qed.

Lemma alloc_get_frame_new :
  forall T S {eqS : EqDec S eq} mode mem (stamp : S) (frame : list T) b mem'
         (ALLOC : Mem.alloc mode mem stamp frame = (b, mem')),
    Mem.get_frame mem' b = Some frame.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b) as [E | E]; auto.
  congruence.
Qed.

Lemma get_frame_upd_frame_eq :
  forall T S {eqS : EqDec S eq}
         (m : Mem.t T S) b f m'
         (UPD : Mem.upd_frame m b f = Some m'),
    Mem.get_frame m' b = Some f.
Proof.
  intros.
  erewrite Mem.get_upd_frame; eauto.
  destruct (equiv_dec b b); eauto.
  congruence.
Qed.

Lemma get_frame_upd_frame_neq :
  forall T S {eqS : EqDec S eq}
         (m : Mem.t T S) b b' f m'
         (UPD : Mem.upd_frame m b f = Some m')
         (NEQ : b' <> b),
    Mem.get_frame m' b' = Mem.get_frame m b'.
Proof.
  intros.
  erewrite Mem.get_upd_frame; eauto.
  destruct (equiv_dec b b'); congruence.
Qed.

Lemma get_frame_store_neq :
  forall T S {eqS : EqDec S eq}
         (m : memory T S) b b' off a m'
         (STORE : store b off a m = Some m')
         (NEQ : b' <> b),
    Mem.get_frame m' b' = Mem.get_frame m b'.
Proof.
  unfold store.
  intros.
  destruct (Mem.get_frame m b) as [f|] eqn:FRAME; try congruence.
  destruct (update_list_Z off a f) as [f'|] eqn:NEWFRAME; try congruence.
  eapply get_frame_upd_frame_neq; eauto.
Qed.

Lemma alloc_get_frame_eq :
  forall T S (eqS : EqDec S eq) m s (mem : memory T S) f b mem',
    Mem.alloc m mem s f = (b, mem') ->
    Mem.get_frame mem' b = Some f.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b); congruence.
Qed.

Lemma alloc_get_frame_neq :
  forall T S (eqS : EqDec S eq) m s (mem : memory T S) f b b' mem',
    Mem.alloc m mem s f = (b, mem') ->
    b <> b' ->
    Mem.get_frame mem' b' = Mem.get_frame mem b'.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b'); congruence.
Qed.

Definition extends {T S} (m1 m2 : memory T S) : Prop :=
  forall b fr, Mem.get_frame m1 b = Some fr -> Mem.get_frame m2 b = Some fr.

Lemma extends_refl : forall {T S} (m : memory T S), extends m m.
Proof. unfold extends. auto. Qed.

Lemma extends_trans : forall {T S} (m1 m2 m3 : memory T S), extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof. unfold extends. auto. Qed.

Lemma extends_load {T S} (m1 m2 : memory T S) b off a :
  forall (EXT : extends m1 m2)
         (DEF : load b off m1 = Some a),
    load b off m2 = Some a.
Proof.
  intros.
  unfold load in *.
  destruct (Mem.get_frame m1 b) as [fr|] eqn:FRAME; inv DEF.
  erewrite EXT; eauto.
Qed.

Definition valid_address {T S} b off (m: memory T S) :=
  exists v, load b off m = Some v.

Lemma extends_valid_address: forall {T S} (b : block S) (m m' : memory T S) off
                                    (VALID : valid_address b off m)
                                    (EXT : extends m m'),
                               valid_address b off m'.
Proof.
  intros.
  unfold valid_address in *.
  destruct VALID.
  eauto using extends_load.
Qed.

Lemma valid_address_store_l :
  forall T S (E:EqDec S eq) b off a (m m' : memory T S)
         (STORE : store b off a m = Some m'),
    valid_address b off m.
Proof.
  unfold store, valid_address, load.
  intros.
  destruct (Mem.get_frame m b) as [fr|] eqn:FRAME; try congruence.
  destruct (update_list_Z off a fr) as [fr'|] eqn:FRAME'; try congruence.
  clear - FRAME'.
  unfold update_list_Z, index_list_Z in *.
  destruct (off <? 0)%Z; try congruence.
  gdep fr. gdep fr'. gdep (Z.to_nat off).
  clear.
  intros off.
  induction off as [|off IH]; intros fr' fr H; destruct fr as [|a' fr]; simpl in *; try congruence; eauto.
  destruct (update_list off a fr) as [fr''|] eqn:FRAME''; try congruence.
  eapply IH; eauto.
Qed.

Lemma valid_address_upd: forall T S (E:EqDec S eq) b a b' a' vl (m m' : memory T S),
  valid_address b a m ->
  store b' a' vl m = Some m' ->
  valid_address b a m'.
Proof.
  unfold valid_address; intuition.
  destruct H.
  unfold load, store in *.
  destruct (b == b').
  - inv e.
    destruct (Mem.get_frame m b') eqn:EQ; try congruence.
    destruct (update_list_Z a' vl l) eqn:EQ'; try congruence.
    inv H0.
    rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H2).
    destruct (equiv_dec b'); try congruence.
    unfold update_list_Z, index_list_Z in *.
    destruct (a <? 0)%Z; try congruence.
    destruct (a' <? 0)%Z; try congruence.
    destruct (eq_nat_dec (Z.to_nat a) (Z.to_nat a')).
    + rewrite e0 in *; erewrite update_list_spec; eauto.
    + erewrite <- update_list_spec2; eauto.
  - destruct (Mem.get_frame m b) eqn:EQ; try congruence.
    destruct (Mem.get_frame m b') eqn:EQ'; try congruence.
    destruct (update_list_Z a' vl l0) eqn:E0; try congruence.
    rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H0).
    destruct (equiv_dec b'); try congruence.
    rewrite EQ.
    eauto.
Qed.

Lemma valid_address_store_r :
  forall T S (E:EqDec S eq) b off a (m m' : memory T S)
         (STORE : store b off a m = Some m'),
    valid_address b off m'.
Proof.
  intros.
  eauto using valid_address_store_l, valid_address_upd.
Qed.

Lemma extends_update :
  forall T S (E:EqDec S eq) (m m1 m2 : memory T S) b off a
         (EXT : extends m m1)
         (STORE : store b off a m1 = Some m2)
         (INVALID : ~ valid_address b off m),
    extends m m2.
Proof.
  intros.
  intros b' fr' FRAME'.
  assert (b' <> b).
  { intros NEQ.
    subst.
    destruct (load b off m) as [r|] eqn:LOAD.
    - apply INVALID. unfold valid_address. eauto.
    - eapply valid_address_store_l in STORE.
      destruct STORE as [res RES].
      unfold load in *.
      rewrite FRAME' in LOAD.
      apply EXT in FRAME'.
      rewrite FRAME' in RES.
      congruence. }
  apply EXT in FRAME'.
  rewrite <- FRAME'.
  eapply get_frame_store_neq; eauto.
Qed.

Lemma valid_store: forall T S (E:EqDec S eq) b off v (m : memory T S),
  valid_address b off m ->
  exists m', store b off v m = Some m'.
Proof.
  unfold valid_address, load, store.
  intros.
  destruct H as [v' Hv].
  destruct (Mem.get_frame m b) as [v''|] eqn:FRAME; try congruence.

  exploit valid_update; eauto.
  intros [fr' Hfr'].
  rewrite Hfr'.
  eapply Mem.upd_get_frame; eauto.
Qed.

Section Injections.

Variables T1 T2 S1 S2 : Type.
Context {eqS1 : EqDec S1 eq}
        {eqS2 : EqDec S2 eq}.

Definition meminj := block S2 -> option (block S1).

Inductive match_vals (mi : meminj) : val S1 -> val S2 -> Prop :=
| mv_num : forall z, match_vals mi (Vint z) (Vint z)
| mv_ptr : forall b1 b2 off
                  (BLOCK : mi b2 = Some b1),
             match_vals mi (Vptr b1 off) (Vptr b2 off).
Hint Constructors match_vals.

Variable match_tags : T1 -> T2 -> memory T2 S2 -> Prop.
Variable valid_update : memory T2 S2 -> memory T2 S2 -> Prop.
Hypothesis valid_update_match_tags :
  forall t1 t2 m2 m2',
    match_tags t1 t2 m2 ->
    valid_update m2 m2' ->
    match_tags t1 t2 m2'.

Inductive match_atoms (mi : meminj) : Atom T1 S1 -> Atom T2 S2 -> memory T2 S2 -> Prop :=
| ma_intro : forall v1 v2 t1 t2 m2
                    (VALS : match_vals mi v1 v2)
                    (TAGS : match_tags t1 t2 m2),
               match_atoms mi (v1, t1) (v2, t2) m2.
Hint Constructors match_atoms.

Definition match_frames (mi : meminj) : list (Atom T1 S1) ->
                                        list (Atom T2 S2) ->
                                        memory T2 S2 ->
                                        Prop :=
  fun f1 f2 m2 => Forall2 (fun a1 a2 => match_atoms mi a1 a2 m2) f1 f2.
Hint Constructors Forall2.
Hint Unfold match_frames.

Record Meminj (m1 : memory T1 S1) (m2 : memory T2 S2) (mi : meminj) := {

  mi_valid : forall b1 b2
                    (INJ : mi b2 = Some b1),
             exists f1 f2,
               Mem.get_frame m1 b1 = Some f1 /\
               Mem.get_frame m2 b2 = Some f2 /\
               match_frames mi f1 f2 m2;

  mi_invalid : forall b2,
                 Mem.get_frame m2 b2 = None ->
                 mi b2 = None;

  mi_inj : forall b1 b2 b2',
             mi b2 = Some b1 ->
             mi b2' = Some b1 ->
             b2 = b2'

}.

(* A weaker version of the corresponding axiom which is easier to use
in some cases *)
Lemma mi_valid' :
  forall m1 m2 mi
         b1 b2 f2
         (INJ : Meminj m1 m2 mi)
         (LOAD : Mem.get_frame m2 b2 = Some f2)
         (MATCH : mi b2 = Some b1),
    exists f1,
      Mem.get_frame m1 b1 = Some f1 /\
      match_frames mi f1 f2 m2.
Proof.
  intros.
  exploit mi_valid; eauto.
  intros [f1 [f2' [H1 [H2 H3]]]].
  rewrite LOAD in H2.
  inv H2.
  eauto.
Qed.

Definition update_meminj (mi : meminj) (b2 : block S2) (b1 : block S1) : meminj :=
  fun b2' =>
    if b2' == b2 then Some b1
    else mi b2'.

Lemma update_meminj_eq : forall mi b2 b1,
                           update_meminj mi b2 b1 b2 = Some b1.
Proof.
  intros.
  unfold update_meminj.
  destruct (@equiv_dec (block _)) as [E | E].
  - trivial.
  - compute in E. intuition.
Qed.
Hint Resolve update_meminj_eq.

Lemma update_meminj_neq : forall mi b2 b1 b2'
                                 (NEQ : b2' <> b2),
                            update_meminj mi b2 b1 b2' = mi b2'.
Proof.
  intros.
  unfold update_meminj.
  destruct (@equiv_dec (block _)) as [E | E].
  - congruence.
  - trivial.
Qed.

Lemma meminj_mem_alloc :
  forall mi mode1 mode2 stamp1 stamp2 m1 b1 m1' f1 m2 b2 m2' f2,
  forall (INJ : Meminj m1 m2 mi)
         (MATCH : match_frames mi f1 f2 m2)
         (E1 :  Mem.alloc mode1 m1 stamp1 f1 = (b1, m1'))
         (E2 : Mem.alloc mode2 m2 stamp2 f2 = (b2, m2'))
         (VALID : valid_update m2 m2'),
    Meminj m1' m2' (update_meminj mi b2 b1).
Proof.
  intros.
  constructor.

  - intros b1' b2' FRAME.
    destruct (b2' == b2) as [E | E].
    + compute in E. subst b2'.
      rewrite update_meminj_eq in FRAME.
      symmetry in FRAME. inv FRAME.
      exists f1.
      erewrite alloc_get_frame_eq; eauto.
      eexists; repeat (split; eauto).
      { erewrite alloc_get_frame_eq; eauto. }
      assert (Hb2 : mi b2 = None).
      { eapply mi_invalid; eauto.
        eapply Mem.alloc_get_fresh; eauto. }
      clear - Hb2 MATCH VALID valid_update_match_tags.
      induction MATCH; eauto.
      constructor; auto.
      inv H.
      inv VALS; eauto.
      constructor; eauto.
      constructor.
      rewrite update_meminj_neq; auto.
      congruence.
    + rewrite update_meminj_neq in FRAME; auto.
      exploit mi_valid; eauto.
      intros [f1' [f2' [H1 [H2 H3]]]].
      exists f1'. exists f2'.
      split; try split.
      * erewrite Mem.alloc_get_frame; eauto.
        destruct (b1 == b1') as [Eb1|Eb1]; trivial.
        compute in Eb1. subst b1'.
        erewrite Mem.alloc_get_fresh in H1; eauto; try congruence.
      * erewrite Mem.alloc_get_frame; eauto.
        destruct (b2 == b2') as [Eb1|Eb1]; try congruence.
      * clear H1 H2.
        induction H3; auto.
        constructor; auto.
        inv H.
        constructor; eauto.
        inv VALS; auto.
        constructor.
        rewrite update_meminj_neq; eauto.
        cut (mi b2 = None); try congruence.
        eapply mi_invalid; eauto.
        erewrite Mem.alloc_get_fresh; eauto.

  - intros b2' H.
    erewrite Mem.alloc_get_frame in H; eauto.
    destruct (b2 == b2'); try congruence.
    rewrite update_meminj_neq; eauto.
    eapply mi_invalid; eauto.

  - unfold update_meminj.
    intros b1' b2' b2'' H1 H2.
    destruct (@equiv_dec (block _)) as [H1' | H1'].
    + inv H1.
      destruct (@equiv_dec (block _)) as [H2' | H2'].
      * congruence.
      * eapply mi_valid in H2; eauto.
        destruct H2 as [f1' [_ [contra [_ _]]]].
        eapply Mem.alloc_get_fresh in E1.
        congruence.
    + destruct (@equiv_dec (block _)) as [H2' | H2'].
      * inv H2.
        eapply mi_valid in H1; eauto.
        destruct H1 as [f1' [_ [contra [_ _]]]].
        eapply Mem.alloc_get_fresh in E1.
        congruence.
      * eapply mi_inj; eauto.

Qed.

Definition match_oframes mi of1 of2 m2 :=
  match_options (fun f1 f2 => match_frames mi f1 f2 m2) of1 of2.

Lemma zreplicate_match_oframes :
  forall z mi a1 a2 m2,
    match_atoms mi a1 a2 m2 ->
    match_oframes mi (zreplicate z a1) (zreplicate z a2) m2.
Proof.
  unfold match_oframes.
  intros.
  unfold zreplicate.
  destruct (ZArith_dec.Z_lt_dec z 0); constructor.
  gdep (BinInt.Z.to_nat z).
  clear - H.
  intros n.
  induction n; simpl; auto.
Qed.

Lemma add_defined : forall mi v11 v12 v21 v22 r2
                           (ADD : add v21 v22 = Some r2)
                           (V1 : match_vals mi v11 v21)
                           (V2 : match_vals mi v12 v22),
                      exists r1,
                        add v11 v12 = Some r1 /\
                        match_vals mi r1 r2.
Proof.
  intros.
  inv V1; inv V2; simpl in *; inv ADD; eauto.
Qed.

Lemma sub_defined : forall mi v11 v12 v21 v22 r2
                           (SUB : sub v21 v22 = Some r2)
                           (V1 : match_vals mi v11 v21)
                           (V2 : match_vals mi v12 v22),
                      exists r1,
                        sub v11 v12 = Some r1 /\
                        match_vals mi r1 r2.
Proof.
  intros.
  inv V1; inv V2; simpl in *; eauto; try congruence;
  try match goal with
        | H : context[if ?b then _ else _] |- _ =>
          destruct b as [E | E]; compute in E; subst; try congruence
      end;
  allinv;
  eauto.
  match goal with
    | H1 : ?x = _,
      H2 : ?x = _ |- _ =>
      rewrite H2 in H1; inv H1
  end.
  match goal with
    | |- context[if ?b then _ else _] =>
      destruct b as [E | E]; try congruence
  end.
  eauto.
Qed.

Lemma match_vals_eq :
  forall m1 m2 mi v11 v12 v21 v22
         (INJ : Meminj m1 m2 mi)
         (VALS1 : match_vals mi v11 v21)
         (VALS2 : match_vals mi v12 v22),
    match_vals mi (val_eq v11 v12)
                  (val_eq v21 v22).
Proof.
  intros. unfold val_eq.
  destruct (v11 == v12) as [E1 | E1]; compute in E1; subst;
  destruct (v21 == v22) as [E2 | E2]; compute in E2; subst;
  auto;
  inv VALS1; inv VALS2; try congruence.
  cut (b2 = b3); try congruence.
  eapply mi_inj; eauto.
Qed.

Lemma match_frames_valid_index :
  forall mi f1 f2 off a2 m2
         (FRAMES : match_frames mi f1 f2 m2)
         (INDEX : index_list_Z off f2 = Some a2),
    exists a1,
      index_list_Z off f1 = Some a1 /\
      match_atoms mi a1 a2 m2.
Proof.
  unfold index_list_Z.
  intros.
  destruct (BinInt.Z.ltb off 0); try congruence.
  gdep (BinInt.Z.to_nat off). clear off.
  induction FRAMES; intros off INDEX; destruct off;
  simpl in *; try congruence; eauto.
  inv INDEX. eauto.
Qed.

Lemma meminj_load :
  forall m1 m2 mi b1 b2 off a2
         (INJ : Meminj m1 m2 mi)
         (LOAD : load b2 off m2 = Some a2)
         (MATCH : mi b2 = Some b1),
    exists a1,
      load b1 off m1 = Some a1 /\
      match_atoms mi a1 a2 m2.
Proof.
  unfold load.
  intros.
  destruct (Mem.get_frame m2 b2) as [f2|] eqn:E2; try congruence.
  exploit mi_valid'; eauto.
  intros [f1 [H1 H2]].
  rewrite H1.
  eapply match_frames_valid_index; eauto.
Qed.

Lemma match_frames_update_success :
  forall mi f1 f2 f2' off a1 a2 m2
         (FRAMES : match_frames mi f1 f2 m2)
         (ATOMS : match_atoms mi a1 a2 m2)
         (INDEX : update_list_Z off a2 f2 = Some f2'),
    exists f1',
      update_list_Z off a1 f1 = Some f1' /\
      match_frames mi f1' f2' m2.
Proof.
  unfold update_list_Z.
  intros.
  destruct (BinInt.Z.ltb off 0); try congruence.
  gdep (BinInt.Z.to_nat off). clear off.
  gdep f2'.
  induction FRAMES; intros f2' off INDEX; destruct off;
  simpl in *; try congruence; eauto.
  - inv INDEX. eauto.
  - match goal with
      | H : (match ?UP with _ => _ end) = Some _ |- _ =>
        destruct UP eqn:E; try congruence
    end.
    inv INDEX.
    exploit IHFRAMES; eauto.
    intros [? [H1 H2]].
    rewrite H1.
    eauto.
Qed.

Lemma match_atoms_valid_update :
  forall mi a1 a2 m2 m2'
         (ATOMS : match_atoms mi a1 a2 m2)
         (VALID : valid_update m2 m2'),
    match_atoms mi a1 a2 m2'.
Proof. intros. inv ATOMS; eauto. Qed.
Hint Resolve match_atoms_valid_update.

Lemma match_frames_valid_update :
  forall mi f1 f2 m2 m2'
         (FRAMES : match_frames mi f1 f2 m2)
         (VALID : valid_update m2 m2'),
    match_frames mi f1 f2 m2'.
Proof. intros. induction FRAMES; eauto. Qed.
Hint Resolve match_frames_valid_update.

Lemma match_frames_upd_frame :
  forall m1 m2 m2' mi
         b1 b2 f1 f2
         (INJ : Meminj m1 m2 mi)
         (FRAMES : match_frames mi f1 f2 m2)
         (UPD : Mem.upd_frame m2 b2 f2 = Some m2')
         (MATCH : mi b2 = Some b1)
         (VALID : valid_update m2 m2'),
    exists m1',
      Mem.upd_frame m1 b1 f1 = Some m1' /\
      Meminj m1' m2' mi.
Proof.
  intros.
  exploit mi_valid; eauto.
  intros [f1' [_ [Hf1' [_ _]]]].
  eapply Mem.upd_get_frame in Hf1'.
  destruct Hf1' as  [m1' Hf1].
  eexists.
  split; eauto.
  constructor.

  - clear - INJ UPD MATCH FRAMES Hf1 VALID valid_update_match_tags.
    intros b1' b2' Hb1b2.
    eapply Mem.get_upd_frame with (b' := b2') in UPD.
    destruct (b2 == b2') as [EQ|NEQ]; try congruence.
    + rewrite UPD.
      compute in EQ; subst b2'.
      assert (b1 = b1') by congruence.
      subst b1'. clear Hb1b2.
      erewrite Mem.get_upd_frame; eauto.
      match goal with
        | |- context[if ?b then _ else _] =>
          destruct b; eauto; try congruence
      end.

      repeat eexists. eauto.
    + rewrite UPD.
      clear UPD FRAMES.
      exploit mi_valid; eauto.
      intros [f1' [f2' [H1 [H2 H3]]]].
      repeat eexists; eauto.
      erewrite Mem.get_upd_frame; eauto.
      match goal with
        | |- context[if ?b then _ else _] =>
          destruct b as [EQ|_]; try congruence
      end.
      compute in EQ. subst b1.
      cut (b2 = b2'); try congruence.
      eapply mi_inj; eauto.

  - intros b2' H.
    destruct (mi b2') as [f2'|] eqn:Eb2'; trivial.
    exploit mi_valid; eauto.
    intros [? [? [? [? ?]]]].
    erewrite Mem.get_upd_frame in H; eauto.
    destruct (b2 == b2'); congruence.

  - eapply mi_inj; eauto.

Qed.

Lemma meminj_store :
  forall m1 m2 mi
         b1 b2 off a1 a2 m2'
         (INJ : Meminj m1 m2 mi)
         (STORE : store b2 off a2 m2 = Some m2')
         (VALS : match_atoms mi a1 a2 m2)
         (MATCH : mi b2 = Some b1)
         (VALID : valid_update m2 m2'),
    exists m1',
      store b1 off a1 m1 = Some m1' /\
      Meminj m1' m2' mi.
Proof.
  unfold store.
  intros.
  destruct (Mem.get_frame m2 b2) as [f2|] eqn:Ef2; try congruence.
  exploit mi_valid'; eauto.
  intros [f1 [H1 H2]].
  rewrite H1.
  destruct (update_list_Z off a2 f2) eqn:E; try congruence.
  exploit match_frames_update_success; eauto.
  intros [f1' [Ef' ?]].
  rewrite Ef'.
  eapply match_frames_upd_frame; eauto.
Qed.

Lemma meminj_alloc : forall mi size mode2 stamp2 m1 a1 m2 a2 b2 m2',
                     forall (INJ : Meminj m1 m2 mi)
                            (ALLOC : alloc mode2 stamp2 size a2 m2 = Some (b2, m2'))
                            (ATOMS : match_atoms mi a1 a2 m2)
                            (VALID : valid_update m2 m2'),
                     forall mode1 stamp1,
                       exists b1 m1',
                         alloc mode1 stamp1 size a1 m1 = Some (b1, m1') /\
                         Meminj m1' m2' (update_meminj mi b2 b1).
Proof.
  unfold alloc.
  intros.
  eapply zreplicate_match_oframes with (z := size) in ATOMS.
  inversion ATOMS as [H1 H2|f1 f2 FRAMES H1 H2];
  rewrite <- H2 in ALLOC;
  inv ALLOC.
  destruct (Mem.alloc mode1 m1 stamp1 f1) as [b1 m1'] eqn:E.
  exists b1. exists m1'.
  split. reflexivity.
  eapply meminj_mem_alloc; eauto.
Qed.

End Injections.
