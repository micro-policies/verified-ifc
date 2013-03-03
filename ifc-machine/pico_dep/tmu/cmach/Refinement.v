Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils Lattices CLattices.

Require Import TMUInstr.
Require Import Abstract Rules AbstractMachine.

Require Import Concrete ConcreteMachine CodeGen.
Require Import FaultRoutine.

Require Import Simulation.

Set Implicit Arguments.
Local Open Scope Z_scope. 
Coercion Z_of_nat : nat >-> Z.

Section Refinement.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}.

(** The fault handler code *)
Definition faultHandler := CodeGen.faultHandler fetch_rule.
Definition valid_cache {T: Type} (l: list T) := eq tmuCacheSize (length l).
Definition valid_fh {T: Type} (l : list T) := eq privInstSize (length l).

Inductive match_stacks : list (@StkElmt L) ->  list (@CStkElmt L) -> Prop :=
| ms_nil : match_stacks nil nil
| ms_cons_data: forall a s cs, 
                  match_stacks s cs ->
                  match_stacks (AData a :: s) (CData a :: cs)
| ms_cons_ret: forall a r s cs, 
                  match_stacks s cs ->
                  match_stacks (ARet a r:: s) (CRet a r false:: cs).

Inductive match_states : @AS L -> @CS L -> Prop :=
|  ms: forall m i astk cstk pc tmuc fh
              (STKS: match_stacks astk cstk)
              (CACHE: valid_cache tmuc) 
              (FH: valid_fh fh),
         match_states (AState m i astk pc)
                      (CState (tmuc++m) (fh++i) cstk pc false)
.

Check forward_backward_sim.

(** Aux functions yet to be defined - or specified at least *)
Variable drop_cache : list (@Atom L) -> list (@Atom L).
Variable drop_fhandler : list (@Instr L) -> list (@Instr L).
Variable c_to_a_stack : list (@CStkElmt L) -> list (@StkElmt L). 

Axiom drop_cache_correct: forall c m, 
    valid_cache c ->
    drop_cache (c++m) = m.

Axiom drop_fhandler_correct: forall h i, 
    valid_fh h ->
    drop_fhandler (h++i) = i.

Axiom match_stacks_obs : forall s s', 
    match_stacks s s' ->
    c_to_a_stack s' = s.

(** Observing a concete cache is just projecting it a the abstract level *)
Definition observe_cstate (cs: @CS L) : @AS L := 
  match cs with 
    | CState m i s pc p => AState (drop_cache m) (drop_fhandler i) (c_to_a_stack s) pc
  end.

(* DD: Don't be tempted to add success s1 as a hyothesis... *)
Axiom final_step_preserved: 
  forall s1 s2,
    (forall s1', ~ step_rules s1 s1') ->
    (match_states s1 s2) ->
    (forall s2', ~ cstep s2 s2')
    /\ s1 = observe_cstate s2.

Axiom step_preserved: 
  forall s1 s1' s2,
    step_rules s1 s1' ->
    match_states s1 s2 ->
    s1 = observe_cstate s2 /\ (exists s2', cstep s2 s2' /\ match_states s1' s2').

Axiom succ_preserved: 
  forall s1 s2, 
    match_states s1 s2 -> 
    success s1 <-> c_success s2.

Axiom cmach_determ: 
  forall s s' s'', 
    cstep s s' -> 
    cstep s s'' -> 
    s' = s''.
 
Require Import LNIwithEvents.

Let aexec_with_trace := sys_trace step_rules success (fun x => x).
Let cexec_with_trace := sys_trace cstep c_success observe_cstate.

Theorem refinement: forall s1 s2 T, 
                      match_states s1 s2 ->
                      cexec_with_trace s2 T ->
                      aexec_with_trace s1 T. 
Proof.
  eapply forward_backward_sim; eauto.
  exact final_step_preserved.
  exact step_preserved.
  exact succ_preserved.
  exact cmach_determ.
Qed.  

End Refinement.


  
