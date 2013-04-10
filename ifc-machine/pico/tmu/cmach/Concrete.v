Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import CLattices.

Set Implicit Arguments.
Local Open Scope Z_scope.

Section CMach.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}.

(** Definition of states for the concrete machine *)

Inductive CStkElmt := 
| CData : @Atom T -> CStkElmt 
| CRet : @Atom T -> bool -> bool -> CStkElmt.
(* first bool is the type of call (v/void return), second bool is
       saved privilege bit *)
(* CH: not sure which variant is better, but in the Haskell version
       the first bool in CRet is labeled by the same label as the int *)

(* DD: the privileged parts of the states are now separate *)
Record CS  := CState {
  cache: list (@Atom T);
  mem : list (@Atom T);
  fhdl:  list (@Instr T); (* fault handler code *)
  imem : list (@Instr T);
  stk : list CStkElmt;
  pc : @Atom T;
  priv : bool
}.

(** * Cache handling mechanism *)

(* Conversion between abstract labels (T) and tags (Z) *)
Definition opCodeToZ (opcode : OpCode) : Z :=
match opcode with 
| OpNoop => 0
| OpAdd => 1
| OpSub => 2
| OpPush => 3
| OpLoad => 4
| OpStore => 5
| OpJump => 6
| OpBranchNZ => 7
| OpCall => 8
| OpRet => 9
| OpVRet => 10
end.

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


(** Conversion from labels to integers *)
Definition to_mvector (opcode: OpCode) (oplabs: option T * option T * option T)  (pclab: T) : Z * Z * Z * Z * Z :=
   let '(op1lab,op2lab,op3lab) := oplabs in 
   let optlabToZ optl :=
     match optl with
     | None => labToZ bot
     | Some l => labToZ l 
     end in
   (opCodeToZ opcode, optlabToZ op1lab, optlabToZ op2lab, optlabToZ op3lab, labToZ pclab).

(*
Definition from_rvector (tags: Z * Z)  T * T := 
  let (tagr, tagrpc) := tags in
  (ZToLab tagr,ZToLab tagrpc). 
*)

Definition handlerLabel := bot.

(* Build the cache line from mvector parameters. 
NB: Ordering of parameters in memory must match addr* definitions above. *)

Section WithListNotations.

Import ListNotations.

Definition build_cache (opcode: OpCode) (oplabs: option T * option T * option T) (pcl:T): list (@Atom T) := 
let '(optag,tag1,tag2,tag3,pctag) := to_mvector opcode oplabs pcl in
[(optag,handlerLabel); (tag1,handlerLabel); (tag2,handlerLabel); (tag3,handlerLabel); 
 (pctag,handlerLabel); (0,handlerLabel); (0,handlerLabel)]. 

End WithListNotations.

(** Cache spec when reading from, writing to *)
Inductive tag_in_mem (m: list (@Atom T)) addr tagv : Prop := 
| tim_intro : index_list_Z addr m = Some (tagv,handlerLabel) ->
              tag_in_mem m addr tagv.

(* Tests the cache line *)  
Inductive cache_hit (m: list (@Atom T)) opcode oplabs pclab : Prop := 
| ch_intro: forall m_op m_tag1 m_tag2 m_tag3 m_tagpc,
              forall (MVEC: to_mvector opcode oplabs pclab = 
                            (m_op, m_tag1, m_tag2, m_tag3, m_tagpc))
                     (OP: tag_in_mem m addrOpLabel m_op)
                     (TAG1: tag_in_mem m addrTag1 m_tag1)
                     (TAG2: tag_in_mem m addrTag2 m_tag2)
                     (TAG3: tag_in_mem m addrTag3 m_tag3)
                     (TAGPC: tag_in_mem m addrTagPC m_tagpc),
                cache_hit m opcode oplabs pclab. 

Lemma build_cache_hit: forall opcode oplabs pclab,
     cache_hit (build_cache opcode oplabs pclab) opcode oplabs pclab.                          
Proof.
  intros. unfold build_cache. 
  destruct (to_mvector opcode oplabs pclab) as [[[[optag tag1] tag2] tag3] pctag] eqn:?. 
  econstructor; eauto; 
  try unfold addrOpLabel; try unfold addrTag1; try unfold addrTag2; try unfold addrTag3;
  try unfold addrTagPC; unfold index_list_Z; econstructor; reflexivity. 
Qed.

(* Reads the cache line *)
Inductive cache_hit_read (m: list (@Atom T)) : T -> T -> Prop :=
| chr_uppriv: forall m_tagr m_tagrpc,
              forall (TAG_Res: tag_in_mem m addrTagRes m_tagr)
                     (TAG_ResPC: tag_in_mem m addrTagResPC m_tagrpc),
                cache_hit_read m (ZToLab m_tagr) (ZToLab m_tagrpc).

Definition update_cache_spec_mvec (m m': list (@Atom T)) := 
  forall addr, 
    addr <> addrOpLabel ->  addr <> addrTagPC -> 
    addr <> addrTag1 -> addr <> addrTag2 -> addr <> addrTag3 ->
    index_list_Z addr m = index_list_Z addr m'.

Definition update_cache_spec_rvec (m m': list (@Atom T)) := 
  forall addr, 
  addr <> addrTagRes -> 
  addr <> addrTagResPC -> 
  index_list_Z addr m = index_list_Z addr m'.

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
 (forall e, In e dstk -> exists a : @Atom T, e = CData a) ->
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
 (forall e, In e dstk -> exists a : @Atom T, e = CData a) ->
 s1 = s2.
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *. 
  inv H. destruct (H0 (CRet a2 b2 p2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

End CMach.

Notation read_m := index_list_Z.
Notation upd_m := update_list_Z. 
Notation "a ::: b" := ((CData a) :: b)  (at level 60, right associativity).
Hint Constructors cache_hit cache_hit_read.


(* DD: NOT NEEDED ANYMORE. TWO SEPARATE MODES and MEMORIES FOR THE MACHINE *)
(* Inductive check_addr_priv : bool -> Z -> Z -> Prop := *)
(* | cap_priv: forall addr size, check_addr_priv true addr size                    *)
(* | cap_upriv: forall addr size, addr >= size -> check_addr_priv false addr size. *)


(* DD: NOT VALID ANYMORE. KEEP IT FOR THE RECORD *)
(* [runsToEscape Rstep pc0 pc1 s0 s1] expresses that the machine runs without error
from state s0 until the pc is no longer in the segment [pc0,pc1), at which 
point it is state s1. *)
(* Inductive runsToEscape (Rstep: CS -> CS -> Prop) (start_pc end_pc : Z): CS -> CS -> Prop :=
| runsToEscapeDone : forall cs, 
  ~ in_bounds start_pc end_pc cs -> 
  runsToEscape Rstep start_pc end_pc cs cs
| runsToEscapeStep: forall cs cs' cs'', 
  in_bounds start_pc end_pc cs -> 
  Rstep cs cs' -> 
  runsToEscape Rstep start_pc end_pc cs' cs'' -> 
  runsToEscape Rstep start_pc end_pc cs cs''.*)

(* APT: I think the above definition is good enough to define handlerCorrect properly, below.
But it is not constraining enough to prove the kind of composition property we'd like
for composing adjacent fragments.  We want something like:

Lemma runs_to_escape_compose: forall pc0 pc1 pc2 s0 s1 s2,
  runsToEscape pc0 pc1 s0 s1 ->
  fst (pc s1) = pc1 -> 
  runsToEscape pc1 pc2 s1 s2 ->
  runsToEscape pc0 pc2 s0 s2. 

But this is false, because there might be jumps from one segment to the other.
One way out of this is to strengthen runsToEscape so that code can only exit
by (a) falling through; (b) jumping to the illegal address -1; or (c) returning
to an address outside of the entire handler (e.g. >=  privInstSize).  If we then
add hypothesis that [pc0,pc2) is within [0,privInstSize), this lemma should go through. *)

(* A more generalized version that handles runsToEscape might also be useful. 
   It might encode a rule like:

   {P} E1 {Q;R}    {Q} E2 {S;R}
----------------------------------
       {P} E1; E2 {S;R}

where {Q;R} means Q is the post-condition if code falls through
and R is the post-condition if it jumps or returns to some other
address outside of the privileged code segment. *)

