Require Import List.
Require Import Omega.
Require Import EquivDec.

Require Import Utils.
Require Import Instr.
Require Import Memory.

Set Implicit Arguments.
Local Open Scope Z_scope.

Section CMach.

(** Definition of states for the concrete machine *)
Inductive privilege := User | Kernel.
Global Instance privilege_EqDec : EqDec privilege eq.
Proof.
  unfold EqDec.
  destruct x; destruct y;
    try (left; reflexivity);
    right; congruence.
Qed.

Notation Atom := (Atom (val privilege) privilege).
Notation memory := (Mem.t Atom privilege).
Notation PcAtom := (PcAtom (val privilege)).
Notation block := (block privilege).

Variable cblock : block.

Inductive CStkElmt :=
| CData : Atom -> CStkElmt
| CRet : PcAtom -> bool -> bool -> CStkElmt.
(* first bool is the type of call (v/void return), second bool is
       saved privilege bit *)
(* CH: not sure which variant is better, but in the Haskell version
       the first bool in CRet is labeled by the same label as the int *)

Record CS  := CState {
  mem : memory;
  fhdl:  list Instr; (* fault handler code *)
  imem : list Instr;
  stk : list CStkElmt;
  pc : PcAtom;
  priv : bool
}.

Inductive CEvent :=
| CEInt : PcAtom -> memory -> CEvent.

(** * Cache handling mechanism *)

Definition opCodeToZ (opcode : OpCode) : Z :=
match opcode with
| OpNoop     => 0
| OpAdd      => 1
| OpSub      => 2
| OpEq       => 3
| OpPush     => 4
| OpPop      => 5
| OpLoad     => 6
| OpStore    => 7
| OpJump     => 8
| OpBranchNZ => 9
| OpCall     => 10
| OpRet      => 11
| OpVRet     => 12
| OpOutput   => 13
| OpDup      => 14
| OpSwap     => 15
| OpAlloc    => 16
| OpSizeOf   => 17
end.

(* Any number that doesn't occur in the above list. *)
Definition invalidOpCode := 18.

(* Where in the cache the various labels live *)
Definition addrOpLabel  := 0.
Definition addrTag1     := 1.
Definition addrTag2     := 2.
Definition addrTag3     := 3.
Definition addrTagPC    := 4.
Definition addrTagRes   := 5.
Definition addrTagResPC := 6.

(*
APT: non longer relevant, now that we have split memories.
Definition tmuCacheSize := 7.
Definition privInstSize := 1000.
  APT: arbitrary for now, but must be >= size of fault handler code
   DD: If we use this for specifying the complete execution of the fault handler,
   I suspect we want to give the exact size?
*)

(* APT: It should be possible for this to be a completely arbitrary integers,
since it will never be inspected. *)
Definition handlerTag : val privilege := Vint 42%Z.
Definition dontCare : val privilege := Vint (-1)%Z.

(* Build the cache line from mvector parameters.
NB: Ordering of parameters in memory must match addr* definitions above. *)

Section WithListNotations.

Import ListNotations.

(* WARNING TO READERS: The presentation in the paper is a little
   inconsistent with the presentation here: In the paper, the PC slot
   in the input and output parts of the cache line come first; here,
   they come last.  This would be easy but a bit tedious to fix. *)

Definition build_cache
           (opcode: Z)
           (tags: val privilege * val privilege * val privilege)
           (pctag: val privilege): list Atom :=
let '(tag1,tag2,tag3) := tags in
[(Vint opcode,handlerTag);
 (tag1,handlerTag);
 (tag2,handlerTag);
 (tag3,handlerTag);
 (pctag,handlerTag);
 (dontCare,handlerTag);
 (dontCare,handlerTag)].

End WithListNotations.

(** Cache spec when reading from, writing to *)
Inductive tag_in_mem (m: list Atom) addr tagv : Prop :=
| tim_intro : forall t, index_list_Z addr m = Some (tagv,t) ->
              tag_in_mem m addr tagv.

Inductive value_on_cache (m : memory) addr v : Prop :=
| voc_intro : forall t, load (cblock, addr) m = Some (v, t) ->
                        value_on_cache m addr v.

(* Tests the cache line *)
Inductive cache_hit (m: list Atom) opcode tags pctag : Prop :=
| ch_intro: forall tag1 tag2 tag3 tagr tagrpc
                     (UNPACK : tags = (tag1,tag2,tag3))
                     (OP: tag_in_mem m addrOpLabel (Vint opcode))
                     (TAG1: tag_in_mem m addrTag1 tag1)
                     (TAG2: tag_in_mem m addrTag2 tag2)
                     (TAG3: tag_in_mem m addrTag3 tag3)
                     (TAGPC: tag_in_mem m addrTagPC pctag)
                     (TAGR: tag_in_mem m addrTagRes tagr)
                     (TAGRPC: tag_in_mem m addrTagResPC tagrpc),
                cache_hit m opcode tags pctag.

Lemma build_cache_hit: forall opcode tags pctag,
     cache_hit (build_cache opcode tags pctag) opcode tags pctag.
Proof.
  intros. unfold build_cache.
  destruct tags as [[tag1 tag2] tag3] eqn:?.
  econstructor; eauto;
  try unfold addrOpLabel; try unfold addrTag1; try unfold addrTag2; try unfold addrTag3;
  try unfold addrTagPC; unfold index_list_Z; econstructor; reflexivity.
Qed.

(* Reads the cache line *)
Inductive cache_hit_read (m: list Atom) tagr tagrpc : Prop :=
| chr_uppriv: forall (TAG_Res: tag_in_mem m addrTagRes tagr)
                     (TAG_ResPC: tag_in_mem m addrTagResPC tagrpc),
                cache_hit_read m tagr tagrpc.

Definition user_memory_extension (m m' : memory) :=
  forall b fr,
    Mem.stamp b = User ->
    Mem.get_frame m b = Some fr ->
    Mem.get_frame m' b = Some fr.

Definition kernel_memory_extension (m m' : memory) : Prop :=
  forall b fr,
    Mem.stamp b = Kernel ->
    b <> cblock ->
    Mem.get_frame m b = Some fr ->
    Mem.get_frame m' b = Some fr.

(** [fault_handler_memory_update] expresses the changes to the memory
that the fault handler is allowed to do: Every frame that was already
present must stay the same, except for the cache. *)

Definition fault_handler_memory_update (m m': memory) :=
  user_memory_extension m m' /\
  kernel_memory_extension m m'.

Definition update_cache_spec_mvec (m m': memory) :=
  fault_handler_memory_update m m' /\
  (forall addr, addr <> addrOpLabel ->
                addr <> addrTagPC   ->
                addr <> addrTag1    ->
                addr <> addrTag2    ->
                addr <> addrTag3    ->
                load (cblock, addr) m = load (cblock, addr) m').

Definition update_cache_spec_rvec (m m': memory) :=
  fault_handler_memory_update m m' /\
  (forall addr, addr <> addrTagRes ->
                addr <> addrTagResPC ->
                load (cblock, addr) m = load (cblock, addr) m').

Definition cache_hit_mem (m:memory) (opcode:Z)
           (tags: val privilege * val privilege * val privilege) (pctags:val privilege) : Prop :=
  match Mem.get_frame m cblock with
    | None => False
    | Some c => cache_hit c opcode tags pctags
  end.

Definition cache_hit_read_mem (m:memory) (tagr:val privilege) (tagrpc:val privilege) : Prop :=
  match Mem.get_frame m cblock with
    | None => False
    | Some c => cache_hit_read c tagr tagrpc
  end.

(** Machine operations for popping the stack when executing a return instruction.
    And it specs. *)

Inductive c_pop_to_return : list CStkElmt -> list CStkElmt -> Prop :=
| cptr_done: forall a b p s,
   c_pop_to_return ((CRet a b p)::s) ((CRet a b p)::s)
| cptr_pop: forall a s s',
    c_pop_to_return s s' ->
    c_pop_to_return ((CData a)::s) s'.

Lemma c_pop_to_return_ret : forall s1 s2,
  c_pop_to_return s1 s2 ->
  exists a b p s, s2 = (CRet a b p)::s.
Proof.
  induction 1; intros; simpl; eauto.
Qed.

Lemma c_pop_to_return_spec : forall s1 s2,
  c_pop_to_return s1 s2 ->
  exists dstk, exists stk a b p,
    s1 = dstk++(CRet a b p)::stk
    /\ (forall e, In e dstk -> exists a, e = CData a).
Proof.
  induction 1; intros; simpl in *.
  exists nil ; exists s ; exists a ; exists b ; exists p.
  simpl ; split ; eauto.
  intuition.

  destruct IHc_pop_to_return as [dstk [stk [a0 [b0 [p0 [Hs Hdstk]]]]]].
  subst.
  exists ((CData a)::dstk).
  exists stk ; eauto.
  exists a0 ; exists b0 ; exists p0 ; split ; eauto.
  intros. inv H0.
  eauto.
  eapply Hdstk; auto.
Qed.

Lemma c_pop_to_return_spec2: forall  s1 s2 p1 p2 b1 b2 a1 a2 dstk,
 c_pop_to_return (dstk ++ CRet a1 b1 p1 :: s2) (CRet a2 b2 p2 :: s1) ->
 (forall e, In e dstk -> exists a : Atom, e = CData a) ->
 CRet a1 b1 p1 =  CRet a2 b2 p2.
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *.
  inv H. destruct (H0 (CRet a2 b2 p2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

Lemma c_pop_to_return_spec3: forall s1 s2 b1 b2 p1 p2 a1 a2 dstk,
 c_pop_to_return (dstk ++ CRet a1 b1 p1 :: s2) (CRet a2 b2 p2 :: s1) ->
 (forall e, In e dstk -> exists a : Atom, e = CData a) ->
 s1 = s2.
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *.
  inv H. destruct (H0 (CRet a2 b2 p2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

Lemma c_pop_to_return_pops_data: forall cdstk a b p cs,
     (forall a : CStkElmt, In a cdstk -> exists d : Atom, a = CData d) ->
     c_pop_to_return (cdstk ++ CRet a b p :: cs) (CRet a b p :: cs).
Proof.
  induction cdstk; intros.
  simpl; auto. constructor.
  simpl. destruct a.
  constructor. eapply IHcdstk; eauto.
  intros; (eapply H ; eauto ; constructor 2; auto).
  exploit (H (CRet p0 b0 b1)); eauto.
  constructor; auto.
  intros [d Hcont]. inv Hcont.
Qed.

End CMach.

Record CSysCall : Type := {
  csi_arity : nat;
  csi_pc : Z
}.

Definition CSysTable : Type := ident -> option CSysCall.

Notation read_m := index_list_Z.
Notation upd_m := update_list_Z.
Notation "a ::: b" := ((CData a) :: b)  (at level 60, right associativity).
Hint Constructors cache_hit cache_hit_read.
