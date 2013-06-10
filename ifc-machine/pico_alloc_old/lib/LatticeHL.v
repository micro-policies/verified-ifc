Require Import Lattices.

Inductive Lab : Set :=
  | L : Lab
  | H : Lab.

Instance HL : JoinSemiLattice Lab :=
{  bot := L 
;  join l1 l2 :=
     match l1, l2 with
       | H, _ => H
       | _, H => H
       | L, L => L
     end
; flows l1 l2 := 
    match l1, l2 with
      | L, _ => true
      | _, H => true
      | _, _ => false
    end   
}.
Proof.
intros l. destruct l; [left ; auto | right ; congruence].
intros l1 l2; destruct l1, l2; auto.
intros l1 l2 l3. destruct l1, l2, l3; intuition. 
intros l. destruct l ; auto.
intros l1 l2. destruct l1, l2; intuition. 
intros l1 l2. destruct l1, l2; intuition. inversion H0.
auto. 
intros l; destruct l; auto.
intros l1 l2 l3; destruct l1, l2, l3; auto.
intros l1 l2; destruct l1, l2; auto.
intuition. 
intuition. 
intros l1 l2; destruct l1, l2; auto.
intros l1 l2; destruct l1, l2; auto.
intros l1 l2 l; destruct l1, l2, l; auto.
Defined.

(* Lemma join_H_left: forall l,  *)
(*   H \_/ l = H. *)
(* Proof. *)
(*   intros. destruct l; auto. *)
(* Qed. *)

(* Lemma join_H_right: forall l,  *)
(*   l \_/ H = H. *)
(* Proof. *)
(*   intros. destruct l; auto. *)
(* Qed. *)
  
