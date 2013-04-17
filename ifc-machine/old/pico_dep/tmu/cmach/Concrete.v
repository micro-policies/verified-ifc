Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import CLattices.

Set Implicit Arguments.

Section CMach.

Context {T: Type}
        {CLatt: ConcreteLattice T}.

(** Definition of states for the concrete machine *)

Inductive CStkElmt := 
| CData : @Atom T -> CStkElmt 
| CRet : @Atom T -> bool -> bool -> CStkElmt.
(* CH: not sure which variant is better, but in the Haskell version
       the first bool in CRet is labeled by the same label as the int *)
(* second bool is saved privilege bit *)

Record CS  := CState {
  mem : list (@Atom T);
  imem : list (@Instr T);
  stk : list CStkElmt;
  pc : @Atom T;
  priv : bool
}.

Local Open Scope Z_scope.
Definition in_bounds (start_pc: Z) (end_pc: Z) (cs : CS) : Prop := 
  start_pc <= fst (pc cs) < end_pc. 

Lemma in_bounds_dec : forall start_pc end_pc (cs: CS),
  {in_bounds start_pc end_pc cs} + {~ in_bounds start_pc end_pc cs}.
Proof.
  intros. unfold in_bounds. 
  unfold Z.le, Z.lt.
  destruct (start_pc ?= fst (pc cs)); destruct (fst (pc cs) ?= end_pc) ;
    try (right; intuition; discriminate); 
    left; intuition; discriminate. 
Qed. 

(* [runsToEscape Rstep pc0 pc1 s0 s1] expresses that the machine runs without error
from state s0 until the pc is no longer in the segment [pc0,pc1), at which 
point it is state s1. *)
Inductive runsToEscape (Rstep: CS -> CS -> Prop) (start_pc end_pc : Z): CS -> CS -> Prop :=
| runsToEscapeDone : forall cs, 
  ~ in_bounds start_pc end_pc cs -> 
  runsToEscape Rstep start_pc end_pc cs cs
| runsToEscapeStep: forall cs cs' cs'', 
  in_bounds start_pc end_pc cs -> 
  Rstep cs cs' -> 
  runsToEscape Rstep start_pc end_pc cs' cs'' -> 
  runsToEscape Rstep start_pc end_pc cs cs''.

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

(* Just for now, though, I'll define a more constrained version of the run predicate
that requires code to reach end_pc. This should have the desired composition properties. *)
Inductive runsToEnd (Rstep: CS -> CS -> Prop) (start_pc : Z) (end_pc : Z) : CS -> CS -> Prop :=
| runsToEndDone : forall cs,
  start_pc <= end_pc -> (* this is technically useful *)
  fst (pc cs) = end_pc ->
  runsToEnd Rstep start_pc end_pc cs cs
| runsToEndStep: forall cs cs' cs'',
  in_bounds start_pc end_pc cs ->
  Rstep cs cs' ->
  runsToEnd Rstep start_pc end_pc cs' cs'' ->
  runsToEnd Rstep start_pc end_pc cs cs''.

Lemma runs_to_end_compose : forall Rstep pc0 pc1 s0 s1,
  runsToEnd Rstep pc0 pc1 s0 s1 ->
  forall pc2 s2,
  runsToEnd Rstep pc1 pc2 s1 s2 ->
  runsToEnd Rstep pc0 pc2 s0 s2.
Proof.
  induction 1; intros. 
    clear H0.  induction H1. 
      econstructor; eauto. omega. 
      econstructor; eauto.       
      unfold in_bounds in *; omega. 
    econstructor; eauto.
      assert (pc1 <= pc2). inv H2.  auto. unfold in_bounds in H3; omega. 
      unfold in_bounds in *; omega. 
Qed.

(* A more generalized version that handles runsToEscape might also be useful. 
   It might encode a rule like:

   {P} E1 {Q;R}    {Q} E2 {S;R}
----------------------------------
       {P} E1; E2 {S;R}

where {Q;R} means Q is the post-condition if code falls through
and R is the post-condition if it jumps or returns to some other
address outside of the privileged code segment. *)


(* Self contained code: [runsToEnd' pc1 pc2 cs1 cs2] starts at pc2
[pc1] and runs until pc [pc2]. *)
Inductive runsToEnd' (Rstep: CS -> CS -> Prop) : Z -> Z -> CS -> CS -> Prop :=
| runsToEndDone' : forall n cs,
  fst (pc cs) = n -> 
  runsToEnd' Rstep n n cs cs
  (* NC: do we need to worry about [n <= n' <= n'']? *)
| runsToEndStep': forall n n' n'' cs cs' cs'',
  fst (pc cs) = n ->
  Rstep cs cs' ->
  fst (pc cs') = n' ->
  runsToEnd' Rstep n' n'' cs' cs'' -> 
  runsToEnd' Rstep n  n'' cs  cs''.

Lemma runsToEnd'_compose : forall step pc0 pc1 s0 s1,
  runsToEnd' step pc0 pc1 s0 s1 ->
  forall pc2 s2,
  runsToEnd' step pc1 pc2 s1 s2 ->
  runsToEnd' step pc0 pc2 s0 s2.
Proof.
  induction 1; intros.
    auto.
    econstructor; eauto.
Qed.

(* TMU Stuff *)

(* Where in the cache the various labels live *)
Definition addrOpLabel  := 0.
Definition addrTag1     := 1.
Definition addrTag2     := 2.
Definition addrTag3     := 3.
Definition addrTagPC    := 4.
Definition addrTagRes   := 5.
Definition addrTagResPC := 6.

Definition tmuCacheSize := 7.

Definition privDataSize := tmuCacheSize. (* must be at least this big, but could
                                              be bigger if fault handler wants private
                                              storage. *)
Definition privInstSize := 1000. (* arbitrary for now, but must be >= size of fault handler code *)

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

(* TMU action on each instruction.  If rule is in the cache (currently
just a single entry), leave the state unchanged and return
Some(result_tag,result_pc_tag); otherwise, set the state to invoke the
TMU fault handler code and return None. *)

Inductive tag_in_mem (m: list (@Atom T)) addr tagv : Prop := 
| tim_intro : forall l, index_list_Z addr m = Some (tagv,l) ->
           tag_in_mem m addr tagv.
  
Inductive cache_hit (m: list (@Atom T)) : (Z * Z * Z * Z * Z ) -> Prop :=
| ch_intro: forall m_op m_tag1 m_tag2 m_tag3 m_tagpc,
              forall (OP: tag_in_mem m addrOpLabel m_op)
                     (TAG1: tag_in_mem m addrTag1 m_tag1)
                     (TAG2: tag_in_mem m addrTag2 m_tag2)
                     (TAG3: tag_in_mem m addrTag3 m_tag3)
                     (TAGPC: tag_in_mem m addrTagPC m_tagpc),
                cache_hit m (m_op, m_tag1, m_tag2, m_tag3, m_tagpc).

(* reads the cache line in non privileged mode, or ignore it in priv mode *)
Inductive cache_hit_read (m: list (@Atom T)) : bool -> T -> T -> Prop :=
| chr_uppriv: forall m_tagr m_tagrpc,
              forall (TAG_Res: tag_in_mem m addrTagRes m_tagr)
                     (TAG_ResPC: tag_in_mem m addrTagResPC m_tagrpc),
                cache_hit_read m false (ZToLab m_tagr) (ZToLab m_tagrpc)
| chr_ppriv: cache_hit_read m true handlerLabel handlerLabel.

Inductive check_addr_priv : bool -> Z -> Z -> Prop :=
| cap_priv: forall addr size, check_addr_priv true addr size                              
| cap_upriv: forall addr size, addr >= size -> check_addr_priv false addr size.

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

End CMach.

Hint Constructors cache_hit_read check_addr_priv.