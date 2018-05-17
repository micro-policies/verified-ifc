Require Import ZArith. (* omega *)
Require Import List.

(** * Useful tactics *)
Ltac inv H := inversion H; clear H; subst.
Ltac gdep x := generalize dependent x.

(* inv by name of the Inductive relation *)
Ltac invh f :=
    match goal with
      [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

Require Coq.Strings.String. Open Scope string_scope.

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
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
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

Ltac try_exploit l :=
  try (exploit l;
       try solve [eauto];
       let H := fresh "H" in intros H;
       repeat match goal with
                | [H : (exists _, _) |- _ ] => destruct H
                | [H : _ /\ _ |- _ ] => destruct H
              end;
       subst).

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
  apply_f_equal HP; rec_f_equal omega.
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

(* Borrowed from CPDT *)
(* Instantiate a quantifier in a hypothesis [H] with value [v], or,
if [v] doesn't have the right type, with a new unification variable.
Also prove the lefthand sides of any implications that this exposes,
simplifying [H] to leave out those implications. *)

Ltac guess v H :=
 repeat match type of H with
          | forall x : ?T, _ =>
            match type of T with
              | Prop =>
                (let H' := fresh "H'" in
                  assert (H' : T); [
                    solve [ eauto 6 ]
                    | specialize (H H'); clear H' ])
                || fail 1
              | _ =>
                specialize (H v)
                || let x := fresh "x" in
                  evar (x : T);
                  let x' := eval unfold x in x in
                    clear x; specialize (H x')
            end
        end.


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

Ltac allinv' :=
  allinv ;
    (match goal with
       | [ H1:  ?f _ _ = _ ,
           H2:  ?f _ _ = _ |- _ ] => rewrite H1 in H2 ; inv H2
     end).

(* NC: Ltac is not exported from [Section]. This is for simplifying
the existential in [predicted_outcome]. *)
Ltac simpl_exists_tag :=
  match goal with
  | [ H: exists _, ?x = (_,_) |- _ ] => destruct H; subst x; simpl
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
(** * Finite and infinite lists *)

CoInductive colist (A : Type) : Type :=
  | Nil : colist A
  | Cons : A -> colist A -> colist A.

Implicit Arguments Nil [A].

Fixpoint list_to_colist (A : Type) (xs : list A) : colist A :=
  match xs with
  | nil => Nil
  | x :: xs' => Cons x (list_to_colist xs')
  end.

CoFixpoint map_colist (A B: Type) (f: A -> B) (t: colist A) : colist B :=
  match t with
    | Nil => Nil
    | Cons a ta => Cons (f a) (map_colist f ta)
  end.

Definition frob A (t : colist A) : colist A :=
  match t with
    | Cons h t' => Cons h t'
    | Nil => Nil
  end.

Theorem frob_eq : forall A (t : colist A), t = frob t.
  destruct t; reflexivity.
Qed.

(* XXX: This could even be a function *)
Inductive list_prefix_colist {T} : list T -> colist T -> Prop :=
  | lpc_stop : forall c, list_prefix_colist nil c
  | lpc_equal : forall e l c,
      list_prefix_colist l c ->
      list_prefix_colist (e :: l) (Cons e c).

Hint Constructors list_prefix_colist.

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

Lemma index_list_Z_app:
  forall (T : Type)  (l1 l2: list T) (i : Z),
  i = Z.of_nat (length l1) -> index_list_Z i (l1 ++ l2) = index_list_Z 0 l2.
Proof.
  induction l1; intros.
  simpl in *. subst. auto.
  simpl (length (a::l1)) in H.  zify.
  simpl.
  replace i with (i - 1 + 1)%Z by omega.
  erewrite <- index_list_Z_cons by try omega.
  eapply IHl1. omega.
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

Lemma index_list_valid (T:Type): forall n (l:list T) v,
   index_list n l = Some v -> n < length l.
Proof.
  induction n; intros; destruct l; simpl in H.
     inv H.
     inv H.  simpl.  omega.
     inv H.
     pose proof (IHn _ _ H). simpl. omega.
Qed.

Lemma index_list_Z_valid (T:Type): forall i (l:list T) v,
   index_list_Z i l = Some v -> (0 <= i)%Z  /\ (Z.to_nat i < length l)%nat.
Proof.
   intros.
   unfold index_list_Z in H.  destruct ((i <? 0)%Z) eqn:?. inv H.
   split. apply Z.ltb_ge; auto.
   eapply index_list_valid; eauto.
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

Fixpoint update_list_list {A} (new : list A) (old : list A) : list A :=
  match new, old with
    | _, nil => new
    | nil, _ => old
    | n :: new', _ :: old' => n :: update_list_list new' old'
  end.

Lemma index_list_update_list_list (T:Type) :
  forall i (new old : list T),
    (i < length new)%nat ->
    index_list i (update_list_list new old) =
    index_list i new.
Proof.
  induction i as [|i IH];
  intros [|n new] [|o old]; simpl; trivial; try omega.
  intros H.
  apply IH.
  omega.
Qed.

Lemma index_list_Z_update_list_list (T:Type) :
  forall i (new old : list T),
    (i < Z_of_nat (length new))%Z ->
    index_list_Z i (update_list_list new old) =
    index_list_Z i new.
Proof.
  intros.
  unfold index_list_Z.
  generalize (Z.ltb_spec0 i 0).
  intros REFL.
  destruct (i <? 0)%Z; trivial.
  inv REFL.
  assert (POS : (0 <= i)%Z) by omega.
  apply index_list_update_list_list.
  rewrite Z2Nat.inj_lt in H; try omega.
  rewrite Nat2Z.id in H. trivial.
Qed.

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


Lemma index_list_map : forall (A B: Type) m x (e:A) (f: A -> B),
  index_list x m = Some e ->
  index_list x (map f m) = Some (f e).
Proof.
  induction m ; intros.
  - rewrite index_list_nil in *. inv H.
  - destruct x ; simpl in *.
    inv H; auto.
    eauto.
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

Lemma update_list_Some (T: Type): forall (v: T) l n,
  n < length l ->
  exists l', update_list n v l = Some l'.
Proof.
  induction l; intros.
  - inv H.
  - destruct n.
    + simpl.  eauto.
    + simpl. edestruct IHl as [l' E]. simpl in H. instantiate (1:= n). omega.
      eexists. rewrite E. eauto.
Qed.

Lemma filter_cons_inv_strong :
  forall X (l1 : list X) x2 l2
         (f : X -> bool),
    x2 :: l2 = filter f l1 ->
    exists l11 l12,
      l1 = l11 ++ l12 /\
      filter f l11 = x2 :: nil /\
      filter f l12 = l2.
Proof.
  intros X l1.
  induction l1 as [|x1 l1 IH]; simpl; try congruence.
  intros.
  destruct (f x1) eqn:E.
  - exists (x1 :: nil).
    exists l1.
    simpl.
    rewrite E.
    inv H.
    eauto.
  - exploit IH; eauto.
    clear IH.
    intros [l11 [l12 [H1 [H2 H3]]]].
    subst.
    exists (x1 :: l11).
    exists l12.
    simpl.
    rewrite E. eauto.
Qed.

Lemma filter_app :
  forall X (l1 l2 : list X) (f : X -> bool),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1 as [|x l1 IH]; simpl; intros. trivial.
  rewrite IH. destruct (f x); auto.
Qed.

Lemma update_list_Z_Some (T:Type): forall (v:T) l (i:Z),
  (0 <= i)%Z ->
  Z.to_nat i < length l ->
  exists l', update_list_Z i v l = Some l'.
Proof.
  intros. unfold update_list_Z.
  destruct (i <? 0)%Z eqn:?.
  - rewrite Z.ltb_lt in Heqb. omega.
  - eapply update_list_Some; eauto.
Qed.

Lemma update_preserves_length: forall T a (vl:T) m m',
  update_list a vl m = Some m' ->
  length m' = length m.
Proof.
  induction a; intros.
  - destruct m; simpl in *.
    + inv H.
    + inversion H; subst; reflexivity.
  - destruct m; simpl in *.
    + inv H.
    + destruct (update_list a vl m) eqn:?.
      * exploit IHa; eauto.
        inversion H; subst.
        intros eq; rewrite <- eq; reflexivity.
      * inv H.
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

Definition is_some T (o : option T) :=
  match o with
    | Some _ => true
    | None => false
  end.

Definition remove_none {T} (l : list (option T)) :=
  filter (@is_some _) l.

Inductive with_silent {T:Type} := | E (e:T) | Silent.
Notation "T +τ" := (@with_silent T) (at level 1).
Notation " 'τ' " := (Silent) (at level 1).

(** Reflexive transitive closure. *)
Definition op_cons (E: Type) (oe: E+τ) (l: list E) :=
  match oe with
      | E e => e::l
      | Silent => l
  end.


Inductive star (S E: Type) (Rstep: S -> E+τ -> S -> Prop): S -> list E -> S -> Prop :=
  | star_refl: forall s,
      star Rstep s nil s
  | star_step: forall s1 s2 s3 e t t',
      Rstep s1 e s2 -> star Rstep s2 t s3 ->
      t' = (op_cons e t) ->
      star Rstep s1 t' s3.
Hint Constructors star.

Lemma op_cons_app : forall E (e: E+τ) t t', (op_cons e t)++t' = op_cons e (t++t').
Proof. intros. destruct e; reflexivity. Qed.

Lemma star_right : forall S E (Rstep: S -> E+τ -> S -> Prop) s1 s2 t,
                     star Rstep s1 t s2 ->
                     forall s3 e t',
                       Rstep s2 e s3 ->
                       t' = (t++(op_cons e nil)) ->
                       star Rstep s1 t' s3.
Proof.
  induction 1; intros.
  eapply star_step; eauto.
  exploit IHstar; eauto. intros.
  inv H3. rewrite op_cons_app; eauto.
Qed.

Inductive plus (S E: Type) (Rstep: S -> E+τ -> S -> Prop): S -> list E -> S -> Prop :=
  | plus_step: forall s t s' e,
      Rstep s e s' ->
      t = (op_cons e nil) ->
      plus Rstep s t s'
  | plus_trans: forall s1 s2 s3 e t t',
      Rstep s1 e s2 -> plus Rstep s2 t s3 ->
      t' = (op_cons e t) ->
      plus Rstep s1 t' s3.

Hint Constructors star.
Hint Constructors plus.

Lemma plus_right : forall E S (Rstep: S -> E+τ -> S -> Prop) s1 s2 t,
                     plus Rstep s1 t s2 ->
                     forall s3 e t',
                       t' = (t++(op_cons e nil)) ->
                       Rstep s2 e s3 -> plus Rstep s1 t' s3.
Proof.
  induction 1; intros.
  inv H1.
  rewrite op_cons_app. simpl.
  eapply plus_trans; eauto.
  exploit IHplus; eauto.
  inv H2. rewrite op_cons_app.  eauto.
Qed.

Lemma step_star_plus :
  forall (S E: Type)
         (Rstep: S -> E+τ -> S -> Prop) s1 t s2
         (STAR : star Rstep s1 t s2)
         (NEQ : s1 <> s2),
    plus Rstep s1 t s2.
Proof.
  intros. inv STAR. congruence.
  clear NEQ.
  gdep e. gdep s1.
  induction H0; subst; eauto.
Qed.
Hint Resolve step_star_plus.

Lemma star_trans: forall S E (Rstep: S -> E+τ -> S -> Prop) s0 t s1,
  star Rstep s0 t s1 ->
  forall t' s2,
  star Rstep s1 t' s2 ->
  star Rstep s0 (t++t') s2.
Proof.
  induction 1.
  - auto.
  - inversion 1.
    + rewrite app_nil_r.
      subst; econstructor; eauto.
    + subst; econstructor; eauto.
      rewrite op_cons_app; reflexivity.
Qed.



Fixpoint replicate T (a: T) n : list T :=
  match n with
    | O => nil
    | S n => a::(replicate a n)
  end.

Section IfDec.

Variables (P : Prop) (P_dec : {P} + {~P}) (T : Type) (e1 e2 : T).

Lemma if_dec_left : P -> (if P_dec then e1 else e2) = e1.
Proof. intros. destruct P_dec; tauto. Qed.

Lemma if_dec_right : ~P -> (if P_dec then e1 else e2) = e2.
Proof. intros. destruct P_dec; tauto. Qed.

End IfDec.

Section Arith.
Local Open Scope Z_scope.

Lemma basic_arithmetic:
    forall v1 v2, (v2 - v1 =? 0) = (v1 =? v2).
  Proof.
    intuition; destruct (v1 =? v2) eqn:E;
    try (rewrite Z.eqb_eq in *); try (rewrite Z.eqb_neq in *); omega.
  Qed.

End Arith.
