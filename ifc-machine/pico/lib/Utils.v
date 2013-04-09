Require Import ZArith. (* omega *)
Require Import List.

(** * Useful tactics *)
Ltac inv H := inversion H; clear H; subst.
Ltac gdep x := generalize dependent x.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* ---------------------------------------------------------------- *)
(* Tactics for replacing definitional equality with provable equality *)
Module EqualityTactics.
(* NC: Using a module here to show where these equality related defs
start and end.  It appears that [Ltac] defs don't escape from sections
... *)

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof.
auto. Qed.

(* Existentially instantiate a hypothesis. *)
Ltac exploit x :=
 refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

(* NC: need to change the order of the premises, versus [modusponens],
so I can get at the implication [P -> Q] first; the proof of [P] may
generate arbitrarily many subgoals. *)
Lemma cut': forall (P Q: Prop), (P -> Q) -> P -> Q.
Proof. auto. Qed.

(* Like [exploit], but using [cut']. *)
Ltac ecut' x :=
    refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _))
 || refine (cut' _ _ _ (x _ _))
 || refine (cut' _ _ _ (x _))
 || refine (cut' _ _ _ (x)).

(* Like [exact H], but allow indexes to be definitionally different if
   they are provably equal.

   For example, a goal

     H : T a1 ... an
     ---------------
     T b1 ... bn

   is reduced to proving

     a1 = b1, ..., an = bn

   by [exact_f_equal H].
*)
Ltac exact_f_equal h :=
  let h_eq := fresh "h_eq" in
  let t := type of h in
  match goal with
  | [ |- ?g ] =>
    cut (g = t); [ intro h_eq; rewrite h_eq; exact h | f_equal; auto ]
  end.

(* A generalization of [exact_f_equal] to implications.

   This is like [applys_eq] from LibTactics.v, except you do not need
   to specify which vars you want equalities for.  See Software
   Foundations for a description of [applys_eq]:
   http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html#lab869

*)
Ltac apply_f_equal h :=
  let h_specialized := fresh "h_specialized" in
  let t := intro h_specialized; exact_f_equal h_specialized in
  (ecut' h; [t|..]).

(* Solve sub goals with [tac], using [f_equal] to make progress when
   possible
*)
Ltac rec_f_equal tac :=
  tac || (progress f_equal; rec_f_equal tac).

Section Test.

Open Scope nat.

Lemma test_apply_f_equal:
  forall (n1 n2: nat) (P: nat -> list (list nat) -> nat -> Prop),
  (forall a, 0 = a -> a = 0 ->
             P a (((n1+1)::nil)::nil) (n1+n2)) ->
  forall b, P (b - b) (((1+n1)::nil)::nil) (n2+n1).
Proof.
  intros ? ? ? HP ?.
  apply_f_equal HP; rec_f_equal auto.
Qed.

Lemma test_exact_f_equal: forall (n1 n2: nat) (P: nat -> nat -> Prop),
  P (n1+1) (n1+n2) -> P (1+n1) (n2+n1).
Proof.
  intros ? ? ? HP. exact_f_equal HP; omega.
Qed.

Lemma test_rec_f_equal:
  forall (n1 n2: nat) (P: list (list nat) -> nat -> Prop),
  P (((n1+1)::nil)::nil) (n1+n2) -> P (((1+n1)::nil)::nil) (n2+n1).
Proof.
  intros ? ? ? HP. exact_f_equal HP; rec_f_equal omega.
Qed.

End Test.

End EqualityTactics.
Export EqualityTactics.

Ltac eq_H_intros := 
  repeat 
    (match goal with 
      | [  |- _ = _ -> _ ] =>
        intros ?Heq
    end).

Ltac eq_H_getrid := 
  repeat 
    (match goal with 
       | [  |- _ = _ -> _ ] =>
         intros _
     end).

Ltac decEq :=
  match goal with
  | [ |- _ = _ ] => f_equal
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac allinv :=
  repeat 
    match goal with
      | [ H: Some _ = Some _ |- _ ] => inv H
      | [ H: Some _ = None |- _ ] => inv H
      | [ H: None = Some _ |- _ ] => inv H
      | _ => idtac
    end.


(* And basic lemmas *)
Lemma rev_nil_nil (A: Type) : forall (l: list A), 
  rev l = nil ->
  l = nil.
Proof.
  induction l; intros ; auto.
  simpl in *.
  exploit app_eq_nil ; eauto. 
  intros [Hcont1 Hcont2]. 
  inv Hcont2. 
Qed. 

(* Useful functions on lists *)

Set Implicit Arguments.

(* What I wanted to write for group_by (taken from ghc stdlib)
Fixpoint span A (p : A -> bool) (xs : list A) : list A * list A :=
  match xs with
  | nil => (nil,nil)
  | x :: xs' =>
      if p x then
        let (ys,zs) := span p xs' in (x::ys,zs)
      else
        (nil,xs)          
  end.

Fixpoint group_by A (e : A -> A -> bool) (xs : list A) : list (list A) :=
  match xs with
  | nil => nil
  | x::xs' => let (ys,zs) := span (e x) xs' in (x::ys) :: group_by e zs
  end.
Error: Cannot guess decreasing argument of fix. *)

(* What I ended up writing for group_by *)
Require Import Omega.
Require Import Recdef.

Definition span' X (p : X -> bool) : forall (xs : list X),
    {x : list X * list X | le (length (snd x)) (length xs)}.
  refine(
    fix span xs :=
      match xs
      return {x : list X * list X | le (length (snd x)) (length xs)}
      with
        | nil => exist _ (nil,nil) _
        | x :: xs' =>
            if p x then
              exist _ (x :: fst (proj1_sig (span xs')),
                       snd (proj1_sig (span xs'))) _
            else
              exist _ (nil,x::xs') _
      end).
  simpl. omega.
  simpl in *. destruct (span xs'). simpl. omega.
  simpl. omega.
Defined.

Function group_by (A : Type) (e : A -> A -> bool)
                  (xs : list A) {measure length xs}
  : list (list A) :=
  match xs with
  | nil => nil
  | x::xs' => (x :: fst (proj1_sig (span' (e x) xs')))
              :: group_by e (snd (proj1_sig (span' (e x) xs')))
  end.
intros. destruct (span' (e x) xs'). simpl. omega.
Defined.

(* 
Eval compute in group_by beq_nat (1 :: 2 :: 2 :: 3 :: 3 :: 3 :: nil). 
*)

Fixpoint zip_with_keep_rests (A B C : Type) (f : A -> B -> C)
    (xs : list A) (ys : list B) : (list C * (list A * list B)) :=
  match xs, ys with
  | x::xs', y::ys' => 
      let (zs, rest) := zip_with_keep_rests f xs' ys' in
        (f x y :: zs, rest)
  | nil, _ => (nil, (nil, ys))
  | _, nil => (nil, (xs, nil))
  end.

(* 
Eval compute in zip_with_keep_rests plus (1 :: 2 :: 3 :: nil)
                                         (1 :: 1 :: nil).

Eval compute in zip_with_keep_rests plus (1 :: 1 :: nil)
                                         (1 :: 2 :: 3 :: nil).
*)

Definition zip_with (A B C : Type) (f : A -> B -> C)
    (xs : list A) (ys : list B) : list C :=
  fst (zip_with_keep_rests f xs ys).

Fixpoint consecutive_with (A B : Type) (f : A -> A -> B) (xs : list A)
    : list B :=
  match xs with
  | nil => nil
  | x1 :: xs' =>
    match xs' with
    | nil => nil
    | x2 :: xs'' => f x1 x2 :: consecutive_with f xs'
    end
  end.

Definition consecutive (A : Type) := consecutive_with (@pair A A).

(*
Eval compute in consecutive (1 :: 2 :: 3 :: 4 :: 5 :: nil).
*)

Fixpoint last_with (A B : Type) (f : A -> B) (l : list A) (d : B) : B :=
  match l with
  | nil => d
  | a :: nil => f a
  | a :: l => last_with f l d
  end.

Definition last_opt (A : Type) xs := last_with (@Some A) xs None.

(* 
Eval compute in last_opt (1 :: 2 :: 3 :: nil).
Eval compute in last_opt (@nil nat).
*)

Fixpoint snoc (A : Type) (xs : list A) (y : A) : list A :=
  match xs with
  | nil => y :: nil
  | x :: xs' => x :: (snoc xs' y)
  end.

Fixpoint init (X : Type) (xs : list X) : list X :=
  match xs with
  | nil => nil
  | x1 :: xs' =>
    match xs' with
    | nil => nil
    | x2 :: xs'' => x1 :: (init xs')
    end
  end.

(*
Eval compute in init (1 :: 2 :: 3 :: nil).
Eval compute in init (1 :: nil).
Eval compute in init (@nil nat).
*)
(** * Finite and infinite traces *)

CoInductive trace (A : Type) : Type :=
  | TNil : trace A
  | TCons : A -> trace A -> trace A.

Implicit Arguments TNil [A].

Fixpoint list_to_trace (A : Type) (xs : list A) : trace A :=
  match xs with
  | nil => TNil
  | x :: xs' => TCons x (list_to_trace xs')
  end.

CoFixpoint map_trace (A B: Type) (f: A -> B) (t: trace A) : trace B :=
  match t with 
    | TNil => TNil
    | TCons a ta => TCons (f a) (map_trace f ta)
  end.

Definition frob A (t : trace A) : trace A :=
  match t with
    | TCons h t' => TCons h t'
    | TNil => TNil
  end.

Theorem frob_eq : forall A (t : trace A), t = frob t.
  destruct t; reflexivity.
Qed.

Fixpoint index_list A n (xs : list A) : option A :=
  match xs, n with
  | nil, _ => None
  | x :: _, 0 => Some x
  | _ :: xs', S n' => index_list n' xs'
  end.

Lemma index_list_nil : forall A pc, 
  index_list pc nil = @None A .
Proof.
  induction pc; auto.
Qed.

Definition index_list_Z A i (xs: list A) : option A :=
  if Z.ltb i 0 then
    None
  else
    index_list (Z.to_nat i) xs.

Lemma index_list_Z_nil : forall A i, 
  index_list_Z i nil = @None A .
Proof.
  intros. unfold index_list_Z. destruct (i <? 0)%Z. auto. apply index_list_nil. 
Qed.  

Lemma index_list_Z_nat (A: Type) :
  forall l i (v:A), 
    index_list_Z i l = Some v -> 
    index_list (Z.to_nat i) l = Some v.
Proof.
  intros. unfold index_list_Z in *. destruct (i <? 0)%Z. congruence. auto.
Qed.


Lemma index_list_cons (T: Type): forall n a (l:list T),
 index_list n l = index_list (n+1)%nat (a :: l).
Proof.
  intros.
  replace ((n+1)%nat) with (S n) by omega. 
  gdep n. induction n; intros.
  destruct l ; simpl; auto.
  destruct l. auto. 
  simpl. eauto.
Qed. 

Lemma index_list_Z_cons (T: Type): forall i (l1: list T) a, 
  (i >= 0)%Z ->
  index_list_Z i l1 = index_list_Z (i+1) (a::l1).
Proof.
  induction i; intros.
  auto.
  unfold index_list_Z. simpl. 
  replace (Pos.to_nat (p + 1)) with ((Pos.to_nat p)+1)%nat by (zify; omega).
  eapply index_list_cons with (l:= l1) (a:= a) ; eauto. 
  zify; omega.
Qed. 
  
Lemma index_list_Z_eq (T: Type) : forall (l1 l2: list T), 
  (forall i, index_list_Z i l1 = index_list_Z i l2) ->
  l1 = l2.
Proof.
  induction l1; intros.
  destruct l2 ; auto.
  assert (HCont:= H 0%Z). inv HCont. 
  destruct l2.
  assert (HCont:= H 0%Z). inv HCont. 
  assert (a = t). 
  assert (Helper:= H 0%Z). inv Helper. auto.
  inv H0. 
  erewrite IHl1 ; eauto.
  intros. destruct i.
  erewrite index_list_Z_cons with (a:= t); eauto; try omega.
  erewrite H ; eauto.  
  erewrite index_list_Z_cons with (a:= t); eauto; try (zify ; omega).
  erewrite H ; eauto. symmetry. eapply index_list_Z_cons; eauto. zify; omega.
  destruct l1, l2 ; auto.
Qed.

Fixpoint update_list A (n : nat) (y : A) (xs : list A) : option (list A) :=
  match xs, n with
  | nil, _ => None
  | _ :: xs', 0 => Some (y :: xs')
  | a :: xs', S n' => 
    match update_list n' y xs' with 
      | None => None
      | Some l => Some (a::l)
    end
  end.

Lemma update_some_not_nil : forall A (v:A) l a l',
  update_list a v l = Some l' ->
  l' = nil ->
  False.
Proof.
  destruct l; intros.
  destruct a ; simpl in * ; congruence.
  destruct a0 ; simpl in *. congruence.
  destruct update_list.  inv H. 
  congruence.
  congruence.
Qed.


Definition update_list_Z A i y (xs: list A) : option (list A) :=
  if Z.ltb i 0 then
    None
  else
    update_list (Z.to_nat i) y xs.

Lemma update_Z_some_not_nil : forall A (v:A) l i l',
  update_list_Z i v l = Some l' ->
  l' = nil ->
  False.
Proof.
  intros. unfold update_list_Z in *.  destruct (i <? 0)%Z. congruence.
  eapply update_some_not_nil; eauto. 
Qed.


Lemma update_list_Z_nat (A: Type) (v:A) l i l':
  update_list_Z i v l = Some l' -> 
  update_list (Z.to_nat i) v l = Some l'. 
Proof.
  intros. unfold update_list_Z in *. destruct (i <? 0)%Z. congruence.
  auto.
Qed.

Lemma update_list_spec (T: Type) : forall (v: T) l a l',
  update_list a v l = Some l' ->
  index_list a l' = Some v.
Proof.
  induction l ; intros.
  destruct a ; simpl in *; inv H.
  destruct a0 ; simpl in *; inv H; auto.
  case_eq (update_list a0 v l) ; intros ; rewrite H in * ; inv H1.
  auto.
Qed.
  
Lemma update_list_Z_spec (T: Type) : forall (v: T) l a l',
  update_list_Z a v l = Some l' ->
  index_list_Z a l' = Some v.
Proof.
  unfold update_list_Z, index_list_Z. intros. 
  destruct (a <? 0)%Z.  congruence.
  eapply update_list_spec; eauto. 
Qed.

Lemma update_list_spec2 (T:Type) : forall (v:T) l n n' l',
  update_list n v l = Some l' ->
  n <> n' ->
  index_list n' l = index_list n' l'.
Proof.
  induction l; intros.
  destruct n; simpl in *; inv H.  
  destruct n. 
    destruct n'. 
      exfalso; omega. 
      destruct l'; inv H. 
      simpl. auto.
    destruct n'. 
      destruct l'; inv H. 
        destruct (update_list n v l); inv H2. 
        destruct (update_list n v l); inv H2. 
        auto.
      destruct l'; inv H.  
        destruct (update_list n v l); inv H2. 
        simpl. 
        destruct  (update_list n v l) eqn:?; inv H2.  
        eapply IHl; eauto. 
Qed.  


Lemma update_list_Z_spec2 (T:Type) : forall (v:T) l a a' l',
  update_list_Z a v l = Some l' ->
  a' <> a ->
  index_list_Z a' l = index_list_Z a' l'.
Proof.
  unfold update_list_Z, index_list_Z. intros.
  destruct (a <? 0)%Z eqn:?. congruence.
  destruct (a' <? 0)%Z eqn:?. auto.
  eapply update_list_spec2; eauto. 
  apply Z.ltb_ge in Heqb. 
  apply Z.ltb_ge in Heqb0. 
  intro. apply H0. apply Z2Nat.inj; eauto.
Qed.

Lemma app_same_length_eq (T: Type): forall (l1 l2 l3 l4: list T), 
  l1++l2 = l3++l4 -> 
  length l1 = length l3 ->
  l1 = l3.
Proof.
  induction l1; intros; simpl in *.
  destruct l3; auto. inv H0.
  destruct l3. inv H0. simpl in *.
  inv H. erewrite IHl1 ; eauto.
Qed.  

Lemma app_same_length_eq_rest (T: Type): forall (l1 l2 l3 l4: list T), 
  l1++l2 = l3++l4 -> 
  length l1 = length l3 ->
  l2 = l4.
Proof.
  intros.
  exploit app_same_length_eq; eauto.
  intro Heq ; inv Heq.
  gdep l3. induction l3 ; intros; auto.
  simpl in *.
  inv H. eauto.
Qed.
