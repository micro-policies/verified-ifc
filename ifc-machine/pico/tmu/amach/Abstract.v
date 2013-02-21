Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import Monad.
Local Open Scope monad_scope.

Set Implicit Arguments.

Inductive StkElmt {T:Type} := 
| AData : @Atom T -> @StkElmt T
| ARet : @Atom T -> bool -> @StkElmt T.
(* CH: not sure which variant is better, but in the Haskell version
       the bool in ARet is labeled by the same label as the int *)

Record AS {T: Type}  := AState {
  amem : list (@Atom T);
  aimem : list (@Instr T);
  astk : list (@StkElmt T);
  apc : @Atom T  
}.

Definition AMach {T: Type} := STO (@AS T).

(** Record update functions by hand *)

Definition upd_amem T (new_amem : list Atom) (s : @AS T) : AS :=
  {| amem := new_amem;
     aimem := aimem s;
     astk := astk s;
     apc := apc s |}.

Definition upd_aimem T (new_aimem : list Instr) (s : @AS T) : AS :=
  {| amem := amem s;
     aimem := new_aimem;
     astk := astk s;
     apc := apc s |}.

Definition upd_astk T (new_astk : list StkElmt) (s : @AS T) : AS :=
  {| amem := amem s;
     aimem := aimem s;
     astk := new_astk;
     apc := apc s |}.

Definition upd_apc T (new_apc : Atom) (s : @AS T) : AS :=
  {| amem := amem s;
     aimem := aimem s;
     astk := astk s;
     apc := new_apc |}.

(** ** Simple compound monadic actions *)

Definition get_amem {T: Type} : AMach (list Atom) :=
  s <- get_;
  ret (@amem T s).
Definition set_amem {T: Type} (new_amem : list Atom) : AMach unit :=
  s <- get_;
  put (@upd_amem T new_amem s).

Definition get_aimem {T: Type} : AMach (list Instr) :=
  s <- get_;
  ret (@aimem T s).

Definition get_astk {T: Type} : AMach (list StkElmt) :=
  s <- get_;
  ret (@astk T s).
Definition set_astk {T:Type} (new_astk : list StkElmt) : AMach unit :=
  s <- get_;
  put (@upd_astk T new_astk s).

Definition get_apc {T: Type} : AMach Atom :=
  s <- get_;
  ret (@apc T s).
Definition set_apc {T: Type} (new_apc : Atom) : AMach unit :=
  s <- get_;
  put (@upd_apc T new_apc s).

(** ** More interesting compound monadic actions *)

Definition index_amem {T: Type} (i : Z) : AMach Atom :=
  am <- @get_amem T;
  match index_list_Z i am with
  | Some a => ret a
  | None => error_
  end.

Definition update_amem {T: Type} i a : AMach unit :=
  am <- @get_amem T;
  match update_list_Z i a am with
  | Some am' => set_amem am'
  | None => error_
  end.

Definition index_aimem {T: Type} (i : Z) : AMach Instr :=
  imem <- @get_aimem T;
  match index_list_Z i imem with
  | Some a => ret a
  | None => error_
  end.

Definition top {T: Type} (stk: list (@StkElmt T)) : @AMach T StkElmt :=
  match stk with
  | a :: s =>  ret a
  | nil => error_
  end.

Definition pop_astk {T: Type}: AMach StkElmt :=
  stk <- @get_astk T;
  match stk with
  | a :: s =>  set_astk (s) ;; ret a
  | nil => error_
  end.

Definition pop_astk_data {T: Type} : AMach Atom :=
  e <- @pop_astk T;
  match e with
  | AData (v,l) =>  ret (v,l)
  | _ => error_
  end.

Definition peek_astk {T:Type} (n:nat) : AMach StkElmt :=
  stk <- @get_astk T;
  match index_list n stk with
  | Some a => ret a
  | None => error_
  end.

Definition peek_astk_data {T:Type} (n:nat) : AMach Atom :=
  e <- @peek_astk T n;
  match e with
  | AData (v,l) =>  ret (v,l)
  | _ => error_
  end.

Fixpoint find_return {T: Type} stk : option ((@Atom T * bool) * list StkElmt) := 
    match stk with
      | nil => None
      | AData _ :: stk' => find_return stk'
      | ARet a r :: stk' => Some (a,r,stk')
    end.

(* Pop any CData from top of stack; then pop and return contents of CRet.
   Error if no CRet frame found. *)
Definition cut_to_areturn {T:Type} : AMach unit := 
  stk <- @get_astk T;
  match find_return stk with
    | None => error_
    | Some (_,stk') => set_astk stk'
  end
.  

Definition peek_to_areturn {T:Type} : AMach (@Atom T * bool) :=
  stk <- @get_astk T;
  match find_return stk with
    | None => error_
    | Some (arp,_) => ret arp
  end
.

Fixpoint pop_args {T: Type} n : AMach (list StkElmt) := 
  match n with 
    | O => ret nil
    | S m => 
      a <- @pop_astk_data T ;
      l <- pop_args m ;
      ret (l++(AData a::nil))
  end.  

Definition push_astk {T:Type} a : AMach unit :=
  stk <- @get_astk T;
  set_astk (a :: stk).

Fixpoint push_args {T: Type} (args: list StkElmt) : AMach unit := 
  match args with 
    | nil => ret tt
    | a::argss =>
      @push_astk T a ;;
      push_args argss
  end.


(* Drop all the data, and the first return stack element, that is returned *)
(* Termination hit: the size of the stack at the initial call site *)
Fixpoint drop_data {T: Type} n : AMach StkElmt :=
  match n with 
    | O => error_
    | S p =>
      stk <- @get_astk T ;
      match stk with 
        | nil => error_
        | AData _ :: _ => _ <- @pop_astk T ; @drop_data T p
        | a::_ => _ <- @pop_astk T ; ret a
      end
  end.

Lemma drop_data_spec {T: Type} : forall m i pc stk a b,
  In (ARet a b) stk ->
  exists a', exists b', exists stk', exists dstk,   
    drop_data (length stk) (AState m i stk pc) = 
    Some (AState m i stk' pc, ARet a' b')
    /\  stk = dstk++(ARet a' b')::stk'
    /\ (forall e, In e dstk -> exists a, e = @AData T a).
Proof.
  induction stk ; intros; inv H.
  simpl. exists a0; exists b ; exists stk; exists nil; simpl ; intuition. 
  destruct a. 
  simpl. exploit IHstk ; eauto. intros [a' [b' [stk' [dstk [Hdrop [Happ Hdata]]]]]].
  inv Happ. unfold upd_astk ; simpl.
  exists a'; exists b'; exists stk'. exists (AData a :: dstk); eauto.
  split; simpl ; intuition ; eauto.
  simpl. unfold upd_astk ; simpl. 
  exists a ; exists b0 ; exists stk ; exists nil. 
  split ; intuition. 
Qed.

Definition success {T: Type} (a : @AS T) : Prop :=
  match index_list_Z (fst (apc a)) (aimem a) with
  | Some Halt => True
  | _ => False
  end.

Ltac break_success_goal :=
  match goal with
  | [|- context[@success _ ?s]] =>
      unfold success;
      match goal with
      | [|- context[index_list_Z ?idx ?aimem]] =>
         remember (index_list_Z idx aimem) as oinstr;
         destruct oinstr as [i |]; try tauto; destruct i; try tauto
      end
  end.

Ltac break_success_hyp :=
  match goal with
  | [H : success ?s |- _] => gdep H; break_success_goal; intro H
  end.

Ltac break_success := try break_success_goal; repeat break_success_hyp.

Lemma success_dec {T: Type} : forall s, {@success T s} + {~@success T s}.
Proof.
 intro; break_success.
Qed.

Definition low_pc {T: Type} {Latt: JoinSemiLattice T} (o: T) (s: AS) : Prop :=
  snd (apc s) <: o = true.

Lemma low_not_high {T: Type} {Latt: JoinSemiLattice T} : forall o s pc l l',
  low_pc o s ->
  apc s = (pc, l') ->
  l <: l' = true ->
  l <: o = true.
Proof.
  intros.
  unfold low_pc in *. rewrite H0 in H. simpl in *.
  eauto with lat.
Qed.

Ltac step_in id :=
  let tac H := (unfold id in H ; repeat sto_break_succ idtac ; allinv ; 
    simpl @apc in * ; simpl @astk in * ; simpl @aimem in * ; simpl @amem in * ) in
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
  step_in index_aimem;
  step_in get_aimem;
  (step_in get); 
  repeat (destruct index_list_Z; allinv).
  
Ltac fetch_mem :=
  step_in index_amem;
  step_in get_amem;
  case_on index_list_Z;
  step_in get;
  allinv ; 
  simpl in *.

Ltac step_push_astk := 
  (step_in push_astk;
    step_in get_astk;
    step_in set_astk;
    step_in get;
    step_in put;
    unfold upd_astk in *; simpl in * ) . 

Ltac step_set_apc :=
  (step_in @set_apc;
    step_in @get; 
    step_in @put; 
    unfold upd_apc in * ; simpl). 

Ltac step_set_amem :=
  step_in set_amem;
  step_in get;
  unfold upd_amem in * ; 
  simpl in *;
  step_in put.

Ltac step_pop_astk_data :=
  step_in pop_astk_data;
  repeat (match goal with | [ a1: StkElmt |- _ ] => (destruct a1; allinv) end);
  step_in pop_astk;
  step_in get_astk;
  step_in get;
  (match goal with 
     | [ H1: context [ (AState _ _ ?s _)] ,
         H2: context [ (AState _ _ ?s' _)] |- _ ] =>
             (destruct s, s'; try solve [ simpl in * ; allinv])
     | [ H1: context [ (AState _ _ ?s _)] |- _ ] =>
             (destruct s; try solve [ simpl in * ; allinv])
   end);
  repeat (sto_break_succ allinv);
  step_in set_astk;
  step_in get;
  step_in put;
  (unfold upd_astk in *; simpl in *);
  repeat (match goal with | [ a1: Atom |- _ ] => (destruct a1 as [?v ?vl]) ; allinv end).

Lemma pop_args_spec (T: Type): forall n m i stk pc args s, 
  pop_args n (AState m i stk pc) = Some (s,args) ->
  (length args) = n 
  /\ (forall arg, In arg args -> exists a, arg = @AData T a)
  /\ exists stk', stk = (rev args) ++ stk' /\ s = AState m i stk' pc.   
Proof.
  induction n ; intros.
  step_in @pop_args. 
  split; [ auto| split ;[intros; inv H | exists stk; eauto]].
  
  step_in @pop_args. 
  step_pop_astk_data.
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

Lemma push_args_spec T: forall args m i stk pc u s, 
  push_args args (@AState T m i stk pc) = Some (s,u) ->
  s = AState m i ((rev args)++stk) pc. 
Proof.
  induction args ; intros.
  simpl in *. allinv; auto.
  simpl in *.
  unfold upd_astk in H. simpl in H. 
  rewrite app_assoc_reverse.  
  exploit IHargs; eauto. 
Qed.  

Ltac step_pop_astk :=
  step_in pop_astk;
  step_in get_astk;
  step_in get;
  (match goal with
     | [ H1: context [ (AState _ _ ?s _)] ,
         H2: context [ (AState _ _ ?s' _)] |- _ ] =>
             (destruct s, s'; try solve [ simpl in * ; allinv])
     | [ H1: context [ (AState _ _ ?s _)] |- _ ] =>
             (destruct s; try solve [ simpl in * ; allinv])
   end);
  (sto_break_succ idtac) ;
  step_in set_astk;
  step_in get;
  step_in put;
  (unfold upd_astk in *; simpl in *) ;
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
      | [H: ?s = (AState _ _ _ _) |- _ ] => inv H           
    end;
    match b with 
      | true =>  eq_H_intros
      | false => eq_H_getrid
    end;       
    (unfold upd_astk in *; simpl in *).

Lemma drop_data_some T : forall m i pc stk s reta,
  drop_data (length stk) (@AState T m i stk pc) = Some (s,reta) ->
  exists a, exists b, In (ARet a b) stk.
Proof.
  induction stk ; intros; inv H.
  destruct a.
  Case "AData".
  case_on @pop_astk.
  step_in @pop_astk.
  step_in @get_astk.
  step_in @get.
  allinv.
  step_in @set_astk;
  step_in @get;
  step_in @put.
  (unfold upd_astk in *; simpl in *).
  exploit IHstk ; eauto. intros [aa [bb Hin]]. eauto.

  case_on @pop_astk.
  step_in @pop_astk.
  step_in @get_astk.
  step_in @get.
  allinv.
  step_in @set_astk;
  step_in get;
  step_in put. exists a; exists b ; auto. constructor; auto.
Qed.

Hint Resolve @flows_refl @flows_join_right  @flows_join_left.