Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import Monad.

Local Open Scope monad_scope.

Set Implicit Arguments.

(** Definition of states for the concrete machine *)

Inductive CStkElmt {T:Type} := 
| CData : @Atom T -> @CStkElmt T
| CRet : @Atom T -> bool -> bool -> @CStkElmt T.
(* CH: not sure which variant is better, but in the Haskell version
       the first bool in CRet is labeled by the same label as the int *)
(* second bool is saved privilege bit *)

Record CS {T: Type}  := {
  mem : list (@Atom T);
  imem : list (@Instr T);
  stk : list (@CStkElmt T);
  pc : @Atom T;
  priv : bool
}.

Definition CMach {T: Type} := STO (@CS T).

(** Utility functions on states *)

(* NC: [Record] pitfall!

   The record update functions commented out below cause an
   exponential blowup in proof size when chained (4^n record copies
   for n updates), because they copy their argument into all fields,
   and can unfold without requiring any reduction (since they
   reconstruct the record using projections).

   So, instead of copying and projecting, we deconstruct the record
   using a let-binding.  This eliminates the blowup problem, and as
   bonus (which I don't understand), removes the need to explicitly
   [unfold] the updates in proofs.

   APT and NC were experiencing a 30 second Qed, due to this blowup,
   in a proof about a two-instruction sequence :P

*)
Definition upd_mem {T} mem' (r: @CS T): CS :=
  let (mem,imem,stk,pc,priv) := r in Build_CS mem' imem stk pc priv.

Definition upd_imem {T} imem' (r: @CS T): CS :=
  let (mem,imem,stk,pc,priv) := r in Build_CS mem imem' stk pc priv.

Definition upd_stk {T} stk' (r: @CS T): CS :=
  let (mem,imem,stk,pc,priv) := r in Build_CS mem imem stk' pc priv.

Definition upd_pc {T} pc' (r: @CS T): CS :=
  let (mem,imem,stk,pc,priv) := r in Build_CS mem imem stk pc' priv.

Definition upd_priv {T} priv' (r: @CS T): CS :=
  let (mem,imem,stk,pc,priv) := r in Build_CS mem imem stk pc priv'.

(* NC: this scheme is dangerous!
Definition upd_mem T (new_mem : list Atom) (s : @CS T) : CS :=
  {| mem := new_mem;
     imem := imem s;
     stk := stk s;
     pc := pc s;
     priv := priv s|}.
*)

(** ** Simple compound monadic actions *)

Definition get_mem {T: Type} : CMach (list Atom) :=
  s <- get_;
  ret (@mem T s).
Definition set_mem {T: Type} (new_mem : list Atom) : CMach unit :=
  s <- get_;
  put (@upd_mem T new_mem s).

Definition get_imem {T: Type} : CMach (list Instr) :=
  s <- get_;
  ret (@imem T s).

Definition get_stk {T: Type} : CMach (list CStkElmt) :=
  s <- get_;
  ret (@stk T s).
Definition set_stk {T:Type} (new_stk : list CStkElmt) : CMach unit :=
  s <- get_;
  put (@upd_stk T new_stk s).

Definition get_pc {T: Type} : CMach Atom :=
  s <- get_;
  ret (@pc T s).
Definition set_pc {T: Type} (new_pc : Atom) : CMach unit :=
  s <- get_;
  put (@upd_pc T new_pc s).

Definition get_priv {T : Type} : CMach bool :=
  s <- get_;
  ret (@priv T s). 
Definition set_priv {T: Type} (new_priv : bool) : CMach unit :=
  s <- get_;
  put (@upd_priv T new_priv s).

(** ** More interesting compound monadic actions *)

Definition index_mem {T: Type} (i : Z) : CMach Atom :=
  m <- @get_mem T;
  match index_list_Z i m with
  | Some a => ret a
  | None => error_
  end.

Definition update_mem {T: Type} i a : CMach unit :=
  m <- @get_mem T;
  match update_list_Z i a m with
  | Some m' => set_mem m'
  | None => error_
  end.

Definition index_imem {T: Type} (i : Z) : CMach Instr :=
  imem <- @get_imem T;
  match index_list_Z i imem with
  | Some a => ret a
  | None => error_
  end.

Definition top {T: Type} (stk: list (@CStkElmt T)) : @CMach T CStkElmt :=
  match stk with
  | a :: s =>  ret a
  | nil => error_
  end.

Definition pop_stk {T: Type}: CMach CStkElmt :=
  stk <- @get_stk T;
  match stk with
  | a :: s =>  set_stk (s) ;; ret a
  | nil => error_
  end.

Definition pop_stk_data {T: Type} : CMach Atom :=
  e <- @pop_stk T;
  match e with
  | CData (v,l) =>  ret (v,l)
  | _ => error_
  end.

Definition peek_stk {T:Type} (n:nat) : CMach CStkElmt :=
  stk <- @get_stk T;
  match index_list n stk with
  | Some a => ret a
  | None => error_
  end.

Definition peek_stk_data {T:Type} (n:nat) : CMach Atom :=
  e <- @peek_stk T n;
  match e with
  | CData (v,l) =>  ret (v,l)
  | _ => error_
  end.

Fixpoint pop_args {T: Type} n : CMach (list CStkElmt) := 
  match n with 
    | O => ret nil
    | S m => 
      a <- @pop_stk_data T ;
      l <- pop_args m ;
      ret (l++(CData a::nil))
  end.  

Definition push_stk {T:Type} a : CMach unit :=
  stk <- @get_stk T;
  set_stk (a :: stk).

Fixpoint push_args {T: Type} (args: list CStkElmt) : CMach unit := 
  match args with 
    | nil => ret tt
    | a::argss =>
      @push_stk T a ;;
      push_args argss
  end.

Fixpoint find_return {T: Type} stk : option ((@Atom T * bool * bool) * list CStkElmt) := 
    match stk with
      | nil => None
      | CData _ :: stk' => find_return stk'
      | CRet a r p :: stk' => Some ((a,r,p),stk')
    end.


(* Pop any CData from top of stack; then pop and return contents of CRet.
   Error if no CRet frame found. *)
Definition cut_to_return {T:Type} : CMach unit := 
  stk <- @get_stk T;
  match find_return stk with
    | None => error_
    | Some (_,stk') => set_stk stk'
  end
.  

Definition peek_to_return {T:Type} : CMach (@Atom T * bool * bool) :=
  stk <- @get_stk T;
  match find_return stk with
    | None => error_
    | Some (arp,_) => ret arp
  end
.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section CMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {ZToLab : Z -> T}
        {labToZ: T -> Z}
        {handlerLabel: T}.

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

Definition mvector (opcode: OpCode) (op1lab:option T) (op2lab:option T) (op3lab:option T) (pclab: T) :
 Z * Z * Z * Z * Z :=
   let optlabToZ optl :=
     match optl with
     | None => labToZ bot
     | Some l => labToZ l 
     end in
   (opCodeToZ opcode, optlabToZ op1lab, optlabToZ op2lab, optlabToZ op3lab, labToZ pclab).

Definition rvector (tagr:Z) (tagrpc:Z) : T * T :=
   (ZToLab tagr,ZToLab tagrpc). 

(* TMU action on each instruction.
If rule is in the cache (currently just a single entry), 
leave the state unchanged and return Some(result_tag,result_pc_tag); 
otherwise, set the state to invoke the TMU fault handler code and 
return None. *)

Definition check_tags (opcode: OpCode) (op1lab:option T) (op2lab:option T) (op3lab:option T) (pclab:T):  @CMach T (option (T * T)) :=  
  priv <- get_priv;
  if priv then 
    (* completely ignore cache (as in Haskell code) *)
    ret Some (handlerLabel,handlerLabel)
  else
   let '(op,tag1,tag2,tag3,tagpc) := mvector opcode op1lab op2lab op3lab pclab in
   (* check against cache *) 
   [m_op,_] <- index_mem addrOpLabel;
   [m_tag1,_] <- index_mem addrTag1;
   [m_tag2,_] <- index_mem addrTag2;
   [m_tag3,_] <- index_mem addrTag3;
   [m_tagpc,_] <- index_mem addrTagPC;
   if (op =? m_op) &&
      (tag1 =? m_tag1) &&
      (tag2 =? m_tag2) &&
      (tag3 =? m_tag3) &&
      (tagpc =? m_tagpc) then
       [m_tagr,_] <- index_mem addrTagRes;
       [m_tagrpc,_] <- index_mem addrTagResPC;
       ret Some(rvector m_tagr m_tagrpc)
   else 
     (* not in cache: arrange to enter TMU fault handler *)
     update_mem addrOpLabel (op,handlerLabel);;
     update_mem addrTag1 (tag1,handlerLabel);;
     update_mem addrTag2 (tag2,handlerLabel);;
     update_mem addrTag3 (tag3,handlerLabel);;
     update_mem addrTagPC (tagpc,handlerLabel);;
     pc <- get_pc;
     push_stk (CRet pc false false);; 
     set_pc (0,handlerLabel);;  (* address of TMUFault code *)
     set_priv true;;
     ret None
.

(* For binding the results of check_tags *)
Notation "[ x , y ] <- c1 +> c2" := 
  (Bind _ c1 (fun v => match v with 
                         | Some (x, y) => c2 
                         | None => ret tt 
                       end))
  (right associativity, at level 84) : monad_scope.


Definition privDataSize := tmuCacheSize. (* must be at least this big, but could
                                              be bigger if fault handler wants private
                                              storage. *)
Definition privInstSize := 1000. (* arbitrary for now, but must be >= size of fault handler code *)

Definition check_addr_priv (addr:Z) (size:Z) : @CMach T unit :=
  priv <- get_priv;
  if priv then
    ret tt
  else if addr >=? size then
         ret tt
       else 
         error_.

Definition cstep : @CMach T unit :=
  [pcv,pcl] <- @get_pc T;
  check_addr_priv pcv privInstSize;;
  instr <- index_imem pcv;
  match instr with 
    | Noop =>  
      [_,rpcl] <- check_tags OpNoop None None None pcl +> 
      set_pc (pcv + 1, rpcl)

    | Add =>
      (* DD: Could we find way of "binding" those values to the
      current stack, using pop_stk instead of peek_stk?  I'm afraid
      we'll have some hard time during the proof, as check_tags
      potentially changes the control flow and inserts the execution
      of a piece of code...  Thinking more about it, the second option
      (directly popping and then restoring the stack whenever
      check_tag fails) is not that simpler...  *)
      [x1v,x1l] <- peek_stk_data 0%nat; 
      [x2v,x2l] <- peek_stk_data 1%nat;
      [rl,rpcl] <- check_tags OpAdd (Some x1l) (Some x2l) None pcl +>
      pop_stk;;
      pop_stk;;
      push_stk (CData (x1v + x2v, rl));;
      set_pc (pcv + 1, rpcl)

    | Sub =>
      [x1v,x1l] <- peek_stk_data 0%nat;
      [x2v,x2l] <- peek_stk_data 1%nat;
      [rl,rpcl] <- check_tags OpSub (Some x1l) (Some x2l) None pcl +>
      pop_stk;;
      pop_stk;;
      push_stk (CData (x1v - x2v, rl));;
      set_pc (pcv + 1, rpcl)

    | Push (cv,cl) =>
      [_,rpcl] <- check_tags OpPush (Some cl) None None pcl +>
      push_stk (CData (cv,cl));;
      set_pc (pcv + 1, rpcl)

    | Load => 
      [addrv,addrl] <- peek_stk_data 0%nat;
      check_addr_priv addrv privDataSize;;
      [xv,xl] <- index_mem addrv;
      [rl,rpcl] <- check_tags OpLoad (Some addrl) (Some xl) None pcl +>
      pop_stk;;
      push_stk (CData (xv,rl));;
      set_pc (pcv + 1, rpcl)

    | Store => 
      [addrv,addrl] <- peek_stk_data 0%nat;
      check_addr_priv addrv privDataSize;;
      [xv,xl] <- peek_stk_data 1%nat;
      [mv,ml] <- index_mem addrv;
      [rl,rpcl] <- check_tags OpStore (Some addrl) (Some xl) (Some ml) pcl +>
      pop_stk;;
      pop_stk;;
      update_mem addrv (xv,rl);;
      set_pc (pcv + 1, rpcl)

    | Jump => 
      [pcv',pcl'] <- peek_stk_data 0%nat;
      [_,rpcl] <- check_tags OpJump (Some pcl') None None pcl +>
      pop_stk;;
      set_pc (pcv', rpcl)

    | BranchNZ offv => 
      [av,al] <- peek_stk_data 0%nat;
      [_,rpcl] <- check_tags OpBranchNZ (Some al) None None pcl +>
      pop_stk;;
      set_pc (if negb (av =? 0) then pcv+offv else pcv+1,rpcl) 

    | Call a r => 
      [pcv',pcl'] <- peek_stk_data 0%nat;
      [rl,rpcl] <- check_tags OpCall (Some pcl') None None pcl +>
      pop_stk;;
      args <- pop_args a;  
      priv <- get_priv;
      push_stk (CRet (pcv+1, if priv then pcl else rl) r priv);;
      push_args args;;
      set_pc (pcv', if priv then pcl' else rpcl)

    | Ret =>   
      arp <- peek_to_return;  (* find top return or die *)
      let '((pcv',pcl'),r,priv') := arp in
      if r then
        error_
      else
        [_,rpcl] <- check_tags OpRet (Some pcl') None None pcl +>
        cut_to_return;;  
        priv <- get_priv;
        set_pc (pcv', if priv then pcl' else rpcl);;
        set_priv priv'
        
    | VRet =>
      [resv,resl] <- peek_stk_data 0%nat;
      arp <- peek_to_return; 
      let '((pcv',pcl'),r,priv') := arp in
      if r then
        [rl,rpcl] <- check_tags OpVRet (Some resl) (Some pcl') None pcl +>
        cut_to_return;;  
        push_stk (CData (resv,rl));;
        priv <- get_priv; 
        set_pc (pcv', if priv then pcl' else rpcl);;
        set_priv priv'
      else
        error_
    | Halt => error_   (* we're going to distingush sucessful executions
                      by looking at what was the last instruction *)
    end
.

    
Fixpoint n_cstep (n:nat) : CMach unit := 
  match n with 
    | O => ret tt
    | S n => 
      cstep;;
      n_cstep n
  end.

  

(* Success is reaching a Halt state in non-privileged mode and address. *)
Definition success (cs : @CS T) : Prop :=
  match index_list_Z (fst (pc cs)) (imem cs) with
  | Some Halt => is_true (negb (priv cs) && (fst (pc cs) >=? privInstSize))
  | _ => False
  end.

Ltac break_success_goal :=
  match goal with
  | [|- context[success ?s]] =>
      unfold success;
      match goal with
      | [|- context[index_list_Z ?idx ?imem]] =>
         remember (index_list_Z idx imem) as oinstr;
         destruct oinstr as [i |]; try tauto; destruct i; try tauto
      end
  end.

Ltac break_success_hyp :=
  match goal with
  | [H : success ?s |- _] => gdep H; break_success_goal; intro H
  end.

Ltac break_success := try break_success_goal; repeat break_success_hyp.

Lemma success_dec:  forall s, {success s} + {~success s}.
Proof.
 intro; break_success.
 unfold is_true.  destruct (negb (priv s) && (fst (pc s) >=? privInstSize)); intuition. 
Qed.

     

Lemma success_runSTO_None : forall  s,
  success s ->
  runSTO cstep s = None.
Proof.
  intros. break_success. destruct s. simpl in *.
  unfold runSTO; simpl. unfold cstep. simpl.
  destruct pc0. simpl. unfold index_imem, get_imem. simpl in *.
  unfold check_addr_priv. simpl. 
  destruct priv0.  simpl in H.  inversion H. 
  destruct (z >=? privInstSize). simpl. 
  rewrite <- Heqoinstr. reflexivity.
  simpl in H. inversion H. 
Qed.

Ltac step_in id :=
  let tac H := (unfold id in H ; repeat sto_break_succ idtac ; allinv ; 
    simpl @pc in * ; simpl @stk in * ; simpl @imem in * ; simpl @mem in * ) in
  repeat 
    progress (match goal with 
      | [H: id _ = _ |- _ ] => tac H
      | [H: id _ _ = _ |- _ ] => tac H
      | [H: id _ _ _ = _ |- _ ] => tac H
      | [H: id _ _ _ _ = _ |- _ ] => tac H
      | _ => (try case_on id)
    end); 
      cbv iota beta in *; repeat sto_break_succ idtac.

Ltac fetch_instr := 
  step_in index_imem;
  step_in get_imem;
  (step_in get); 
  repeat (destruct index_list_Z; allinv).
  
Ltac fetch_mem :=
  step_in index_mem;
  step_in get_mem;
  case_on index_list_Z;
  step_in get;
  allinv ; 
  simpl in *.

Ltac step_push_astk := 
  (step_in push_stk;
    step_in get_stk;
    step_in set_stk;
    step_in get;
    step_in put;
    unfold upd_stk in *; simpl in *).

Ltac step_set_apc :=
  (step_in @set_pc;
    step_in @get; 
    step_in @put; 
    unfold upd_pc in * ; simpl). 

Ltac step_set_amem :=
  step_in set_mem;
  step_in get;
  unfold upd_mem in * ; 
  simpl in *;
  step_in put.

Ltac step_pop_stk_data :=
  step_in pop_stk_data;
  repeat (match goal with | [ a1: CStkElmt |- _ ] => (destruct a1; allinv) end);
  step_in pop_stk;
  step_in get_stk;
  step_in get;
  (match goal with 
     | [ H1: context [ (Build_CS _ _ ?s _ _)] ,
         H2: context [ (Build_CS _ _ ?s' _ _)] |- _ ] =>
             (destruct s, s'; try solve [ simpl in * ; allinv])
     | [ H1: context [ (Build_CS _ _ ?s _ _)] |- _ ] =>
             (destruct s; try solve [ simpl in * ; allinv])
   end);
  repeat (sto_break_succ allinv);
  step_in set_stk;
  step_in get;
  step_in put;
  (unfold upd_stk in *; simpl in *);
  repeat (match goal with | [ a1: Atom |- _ ] => (destruct a1 as [?v ?vl]) ; allinv end).

Lemma pop_args_spec: forall n m i stk pc priv args s, 
  pop_args n (Build_CS m i stk pc priv) = Some (s,args) ->
  (length args) = n 
  /\ (forall arg, In arg args -> exists a, arg = @CData T a)
  /\ exists stk', stk = (rev args) ++ stk' /\ s = Build_CS m i stk' pc priv.   
Proof.
  induction n ; intros.
  step_in @pop_args. 
  split; [ auto| split ;[intros; inv H | exists stk0; eauto]].
  
  step_in @pop_args. 
  step_pop_stk_data.
  exploit IHn ; eauto. intros [Hlen [Hdata H]].
  destruct H as [stk' [Heqstk Hs]].
  inv Hs. 
  rewrite app_length. 
  simpl. split. 
  omega.

  split.
  intros. apply in_app_or in H. destruct H as [Hv0 | Hrem].
  eapply Hdata; eauto.
  inv Hrem ; eauto. elim H. 
  exists stk'. split ; auto.
  rewrite app_comm_cons; eauto.
  rewrite rev_app_distr with (x:= v0).
  reflexivity.
Qed.

Lemma push_args_spec : forall args m i stk pc priv u s, 
  push_args args (@Build_CS T m i stk pc priv) = Some (s,u) ->
  s = Build_CS m i ((rev args)++stk) pc priv. 
Proof.
  induction args ; intros.
  simpl in *. allinv; auto.
  simpl in *.
  unfold upd_stk in H. simpl in H. 
  rewrite app_assoc_reverse.  
  exploit IHargs; eauto. 
Qed.  

Ltac step_pop_stk :=
  step_in pop_stk;
  step_in get_stk;
  step_in get;
  (match goal with
     | [ H1: context [ (Build_CS _ _ ?s _ _)] ,
         H2: context [ (Build_CS _ _ ?s' _ _)] |- _ ] =>
             (destruct s, s'; try solve [ simpl in * ; allinv])
     | [ H1: context [ (Build_CS _ _ ?s _ _)] |- _ ] =>
             (destruct s; try solve [ simpl in * ; allinv])
   end);
  (sto_break_succ idtac) ;
  step_in set_stk;
  step_in get;
  step_in put;
  (unfold upd_stk in *; simpl in *) ;
  repeat (match goal with | [ a1: Atom |- _ ] => (destruct a1 as [?v ?vl]) end).

Ltac step_pop_args_spec b :=
  case_on pop_args;
  repeat 
    match goal with 
      | [H: pop_args ?n _ = Some _ |- _ ] => 
        (exploit pop_args_spec; eauto) ;
        let Hlen := fresh "Hlen" in
          let Hargs := fresh "Hargs" in
            let stk := fresh "stk" in
              let Hstk := fresh "Hstk" in
                let s := fresh "s" in
                  intros [Hlen [Hargs [stk [Hstk s]]]];
                    (generalize H ; clear H)           
    end;
    match goal with 
      | [H: ?s = (Build_CS _ _ _ _ _) |- _ ] => inv H           
    end;
    match b with 
      | true =>  eq_H_intros
      | false => eq_H_getrid
    end;       
    (unfold upd_stk in *; simpl in *).

End CMachine.
