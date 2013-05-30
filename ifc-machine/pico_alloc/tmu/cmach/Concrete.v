Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.

Set Implicit Arguments.
Local Open Scope Z_scope.

Section CMach.

(** Definition of states for the concrete machine *)

Inductive CStkElmt := 
| CData : @Atom Z -> CStkElmt 
| CRet : @Atom Z -> bool -> bool -> CStkElmt.
(* first bool is the type of call (v/void return), second bool is
       saved privilege bit *)
(* CH: not sure which variant is better, but in the Haskell version
       the first bool in CRet is labeled by the same label as the int *)

Record CS  := CState {
  mem : Mem.t (@Atom Z) ;
  fhdl:  list Instr; (* fault handler code *)
  imem : list Instr;
  stk : list CStkElmt;
  pc : Z * Z;
  priv : bool
}.

Inductive CEvent :=
| CEInt : @Atom Z -> CEvent.

(** * Cache handling mechanism *)

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
| OpOutput => 11
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


(*
(** Conversion from labels to integer tags *)
Definition to_mvector (opcode: OpCode) (labs: T * T * T)  (pclab: T) : Z * Z * Z * Z * Z :=
   let '(lab1,lab2,lab3) := labs in 
   (opCodeToZ opcode, labToZ lab1, labToZ lab2, labToZ lab3, labToZ pclab).
*)

(*
Definition from_rvector (tags: Z * Z)  T * T := 
  let (tagr, tagrpc) := tags in
  (ZToLab tagr,ZToLab tagrpc). 
*)

(* APT: It should be possible for this to be a completely arbitrary integer, 
since it will never be inspected. *)
Definition handlerTag := 42%Z. 

(* Ditto *)
Definition dontCare := (-1)%Z.


(* Build the cache line from mvector parameters. 
NB: Ordering of parameters in memory must match addr* definitions above. *)

Section WithListNotations.

Import ListNotations.

Definition build_cache (opcode: Z) (tags: Z * Z * Z) (pctag:Z): list (@Atom Z) := 
let '(tag1,tag2,tag3) := tags in 
[(Vint opcode,handlerTag); 
  (Vint tag1,handlerTag);
  (Vint tag2,handlerTag);
  (Vint tag3,handlerTag); 
  (Vint pctag,handlerTag);
  (Vint dontCare,handlerTag);
  (Vint dontCare,handlerTag)]. 

End WithListNotations.

(** Cache spec when reading from, writing to *)
Inductive tag_in_mem (m: list (@Atom Z)) addr tagv : Prop := 
| tim_intro : forall tag, index_list_Z addr m = Some (tagv,tag) ->
              tag_in_mem m addr tagv.

(* Tests the cache line *)  
Inductive cache_hit (m: list (@Atom Z)) opcode tags pctag : Prop := 
| ch_intro: forall tag1 tag2 tag3 tagr tagrpc
                     (UNPACK : tags = (tag1,tag2,tag3))
                     (OP: tag_in_mem m addrOpLabel (Vint opcode)) 
                     (TAG1: tag_in_mem m addrTag1 (Vint tag1))
                     (TAG2: tag_in_mem m addrTag2 (Vint tag2))
                     (TAG3: tag_in_mem m addrTag3 (Vint tag3))
                     (TAGPC: tag_in_mem m addrTagPC (Vint pctag))
                     (TAGR: tag_in_mem m addrTagRes (Vint tagr))
                     (TAGRPC: tag_in_mem m addrTagResPC (Vint tagrpc)),
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
Inductive cache_hit_read (m: list (@Atom Z)) : Z -> Z -> Prop :=
| chr_uppriv: forall tagr tagrpc,
              forall (TAG_Res: tag_in_mem m addrTagRes (Vint tagr))
                     (TAG_ResPC: tag_in_mem m addrTagResPC (Vint tagrpc)),
                cache_hit_read m tagr tagrpc.

Definition update_cache_spec_mvec (m m': Mem.t (@Atom Z)) := 
  forall b addr, 
    (b, addr) <> (Mem.cblock, addrOpLabel) ->
    (b, addr) <> (Mem.cblock, addrTagPC) -> 
    (b, addr) <> (Mem.cblock, addrTag1) ->
    (b, addr) <> (Mem.cblock, addrTag2) ->
    (b, addr) <> (Mem.cblock, addrTag3) ->
    Mem.load b addr m = Mem.load b addr m'.

Definition update_cache_spec_rvec (m m': Mem.t (@Atom Z)) := 
  forall b addr, 
  (b, addr) <> (Mem.cblock, addrTagRes) -> 
  (b, addr) <> (Mem.cblock, addrTagResPC) -> 
  Mem.load b addr m = Mem.load b addr m'.


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
  
End CMach.

Notation read_m := index_list_Z.
Notation upd_m := update_list_Z. 
Notation "a ::: b" := ((CData a) :: b)  (at level 60, right associativity).
Hint Constructors cache_hit cache_hit_read.


