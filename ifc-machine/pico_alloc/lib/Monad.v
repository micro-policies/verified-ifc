
Require Import List.
Require Import FunctionalExtensionality.
Require Import Utils.

Set Implicit Arguments.

Class Monad(M:Type->Type) : Type := {
  Return : forall (A:Type), A -> M A ; 
  Bind : forall (A B:Type), M A -> (A -> M B) -> M B ; 
  ret_left_unit : forall A B (x:A) (f:A -> M B), Bind (Return x) f = f x ; 
  ret_right_unit : forall A (c:M A), Bind c (@Return _) = c ; 
  bind_assoc : forall A B C (f:M A) (g:A -> M B) (h:B -> M C), 
    Bind (Bind f g) h = Bind f (fun x => Bind (g x) h)
}.

Notation "'ret' x" := (Return x) (at level 75) : monad_scope.
Notation "x <- c1 ; c2" := (Bind _ c1 (fun x => c2)) 
  (right associativity, at level 84, c1 at next level) : monad_scope.
Notation "c1 ;; c2" := (Bind _ c1 (fun _ => c2))
  (right associativity, at level 84) : monad_scope.
Notation "[ x , y ] <- c1 ; c2" := 
  (Bind _ c1 (fun v => match v with | (x,y) => c2 end)) 
  (right associativity, at level 84) : monad_scope.


Definition STO(S A : Type) := S -> option (S * A).

Instance ErrorStateMonad(S : Type) : Monad (STO S) := { 
  Return := fun A x s => Some (s,x);
  Bind := fun A B c f s =>
    match c s with
    | None => None
    | Some (s',x') => f x' s'
    end 
}.
 intros. apply functional_extensionality; auto.
 intros. apply functional_extensionality.
   intro. destruct (c x); trivial; destruct p; auto.
 intros. apply functional_extensionality; auto.
   intros. destruct (f x); trivial; destruct p; auto.
Defined.

(** * Lemmas and tactics for eliminating and introducing a monad *)
Lemma sto_bind_succ_elim: forall (AS A B :Type) 
  (c1: STO AS A) (f: A -> STO AS B) (s1 s2: AS) v,
    Bind _ c1 f s1 = Some (s2, v)
      -> exists s1': AS, exists v',
            c1 s1 = Some (s1', v') /\ f v' s1' = Some (s2, v).
Proof. intros. unfold Bind, ErrorStateMonad in H. 
  destruct (c1 s1) as [(s1', v')| ]; try discriminate. 
  exists s1'; exists v'. tauto.
Qed.

Lemma sto_bind_succ_intro :
  forall (AS A B:Type) (c1:STO AS A) (f: A -> STO AS B) (s1 s2 s1':AS)
    (v':A) (v:B),
    c1 s1 = Some (s1', v') -> f v' s1' = Some (s2, v)
      -> Bind _ c1 f s1 = Some (s2, v).
Proof. intros. unfold Bind, ErrorStateMonad. rewrite H. trivial. Qed.

Lemma sto_bind_fail_elim :
  forall (AS A B:Type) (c1:STO AS A) (f: A -> STO AS B) (s1:AS),
    Bind _ c1 f s1 = None
      -> (c1 s1) = None \/
         (exists s1': AS, exists v':A,
            c1 s1 = Some (s1', v') /\ f v' s1' = None).
Proof. intros. unfold Bind, ErrorStateMonad in H. 
  destruct (c1 s1) as [(s1', v')| ]; try discriminate.
  right. exists s1'; exists v'. tauto.
  left. trivial.
Qed.

(** Find a (v <- op1; op2) s = Some (s', v') in the context; break
 ** it using sto_bind_succ_elim; introduce the intermediate state 
 ** and value into the context; try the input tactic *)
Ltac sto_break_succ tac := 
  match goal with
    | [H: Bind _ _ _ ?s = Some (?s', ?v') |- _]  => 
      apply sto_bind_succ_elim in H; 
      let H1 := fresh "H" in let s' := fresh "s" in let v' := fresh "v" in 
        destruct H as [s' [v' [H1 H]]]; tac
  end.

(** Find a (v <- op1; op2) s = None in the context; break
 ** it using mach_monad_fail_elim; destruct the goal into two cases *)
Ltac sto_break_fail := 
  match goal with
    | [H: Bind _ _ _ ?s = None |- _]  => 
      apply sto_bind_fail_elim in H;
      destruct H as [H|H];
      [idtac|
        let H1 := fresh "H" in let s' := fresh "s" in let v' := fresh "v" in 
        destruct H as [s' [v' [H1 H]]]]
  end.

Definition get S : STO S S :=
  fun s => Some (s, s).

Definition put S (s : S) : STO S unit :=
  fun _ => Some (s, tt).

Definition error S A : STO S A :=
  fun s => None.

(* XXX It's strange that we can't use get directly;
   in Coq 8.4 the error message is more informative:
   "Error: Cannot infer the implicit parameter M of Bind." *)
Notation "'get_'" := (@get _).
Notation "'error_'" := (@error _ _).

Ltac allinv :=
  repeat 
    match goal with
      | [ H1: Some _ = Some _ |- _ ] => inv H1
      | [ H1: Some _ = None |- _ ] => inv H1
      | [ H1: None = Some _ |- _ ] => inv H1
      | [ H1: Return _ _ = Some _ |- _ ] => inv H1
      | [ H1: Some _  = Return _ _ |- _ ] => inv H1
      | [ H1: @error _ _ _ = Some _ |- _ ] => inv H1
      | [ H1: Some _ = @error _ _ _ |- _ ] => inv H1
      | _ => idtac
    end.

Lemma invert_if_monad S : forall (b: bool) (s s': S) u,
  (if b then Return tt else error_) s = Some (s', u) ->
  b = true.
Proof.
  intros. destruct b; allinv.
  auto.
Qed.

Lemma simpl_match_2 S : forall A B C (f: A -> B -> option C) g x y (s s' s'': S),
  match f x y with
    | Some am' => g am'
    | None => error_
  end s' = Some (s'', tt) ->
  exists am, f x y = Some am.
Proof.
  intros.
  case_eq (f x y) ; intros; (rewrite H0 in H); eauto.
  allinv.
Qed.

Lemma simpl_match_3 S : forall A B C D (f: A -> B -> C -> option D) g x y z (s s' s'': S),
  match f x y z with
    | Some am' => g am'
    | None => error_
  end s' = Some (s'', tt) ->
  exists am, f x y z = Some am.
Proof.
  intros.
  case_eq (f x y z) ; intros; (rewrite H0 in H); eauto.
  allinv.
Qed.


Definition runSTO S : STO S unit -> S -> option S :=
  fun sto => fun s => 
    match sto s with
    | None => None
    | Some (x,_) => Some x
    end.

Lemma runSTO_some S : forall c (s s':S), 
  runSTO c s = Some s' ->
  c s = Some (s' , tt).
Proof.
  intros. unfold runSTO in H.
  destruct (c s).  
  destruct p. 
  destruct u.
  congruence.
  congruence.
Qed.

Lemma runSTO_none S : forall c (s:S), 
  runSTO c s = None ->
  c s = None.
Proof.
  intros. unfold runSTO in H.
  destruct (c s).  
  destruct p. 
  destruct u.
  congruence.
  congruence.
Qed.

Ltac runSTO_hint := 
  match goal with
    | [H: runSTO _ _ = Some _ |- _]  => apply runSTO_some in H 
    | [H: runSTO _ _ = None |- _]  => apply runSTO_none in H
  end; try runSTO_hint.


(* DD: I know this is ugly. Suggestions welcome. *)
Ltac case_on id :=
  repeat
    (match goal with 
       | [ H: context [ id ?v ]  |- _ ] =>
         let x := fresh "id" in
           (remember (id v) as x) ; 
           match goal with 
             | [ Heq: x = (id v) |- _ ] => 
               destruct x ; allinv ; symmetry in Heq ;
                 match goal with
                   | [ Heq: id v = Some ?p |- _ ] =>
                     destruct p ; generalize Heq ; clear Heq
                 end
           end
       | [ H: context [ id ?v ?s ]  |- _ ] =>
         let x := fresh "id" in
           (remember (id v s) as x) ; 
           match goal with 
             | [ Heq: x = (id v s) |- _ ] => 
               destruct x ; allinv ; symmetry in Heq ;
                 match goal with
                   | [ Heq: id v s = Some ?p |- _ ] =>
                     destruct p ; generalize Heq ; clear Heq
                 end
           end
       | [ H: context [ id ?v ?s ?t ]  |- _ ] =>
         let x := fresh "id" in
           (remember (id v s t) as x) ; 
           match goal with 
             | [ Heq: x = ?p |- _ ] => 
               destruct x ; allinv ; symmetry in Heq ;
                 match goal with
                   | [ Heq: id v s t = Some ?p |- _ ] =>
                     destruct p ; generalize Heq ; clear Heq
                 end            
           end
    | [ H: context [ @id ?h ?v ?s ?t ]  |- _ ] =>
      let x := fresh "id" in
        (remember (@id h v s t) as x) ;
        match goal with 
             | [ Heq: x = ?p |- _ ] => 
               destruct x ; allinv ; symmetry in Heq ;
                 match goal with
                   | [ Heq: @id h v s t = Some ?p |- _ ] =>
                     destruct p ; generalize Heq ; clear Heq
                 end            
           end
    | [ H: context [ @id ?h ?lat ?v ?s ?t ]  |- _ ] =>
      let x := fresh "id" in
        (remember (@id h lat v s t) as x) ;
        match goal with 
             | [ Heq: x = ?p |- _ ] => 
               destruct x ; allinv ; symmetry in Heq ;
                 match goal with
                   | [ Heq: @id h lat v s t = Some ?p |- _ ] =>
                     destruct p ; generalize Heq ; clear Heq
                 end            
           end
     end)
     ; eq_H_intros.    


Local Open Scope monad_scope.
Fixpoint mfold (S A B: Type) (f: A -> B -> STO S B) (l: list A) (b: B): STO S B :=
  match l with
    | nil => ret b
    | h :: t =>
      rhd <- (f h b) ;
      mfold f t rhd
  end.
