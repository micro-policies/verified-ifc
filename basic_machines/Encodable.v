Require Import ZArith.
Require Import Lattices.
Require Import CodeGen.
Require Import Concrete.

Open Scope Z_scope.

(** The type [L] is encodable to integers if we have the following two-way mapping. *)

Class Encodable (L : Type) := {
  labToZ : L -> Z;
  ZToLab : Z -> L;
  ZToLab_labToZ_id : forall l, l = ZToLab (labToZ l)
}.

(** The two-point lattice elements are encodable to integers. *)
Program Instance EncodableHL : Encodable Lab := {

  labToZ l :=
    match l with
      | L => boolToZ false
      | H => boolToZ true
    end

  ;ZToLab z :=
    match z with
      | 0 => L
      | _ => H
    end

}.

Next Obligation. destruct l; auto. Qed.


(** Connecting vectors of encodable labels to triples of concrete (integer) tags. *)
Section Encodable.

Context {T : Type}
        {ET : Encodable T}.

Lemma labToZ_inj: forall (l1 l2: T), labToZ l1 = labToZ l2 -> l1 = l2.
Proof.
  intros.
  rewrite (ZToLab_labToZ_id l1).
  rewrite (ZToLab_labToZ_id l2).
  apply f_equal; auto.
Qed.

Import Vector.VectorNotations.
Local Open Scope nat_scope.

Definition nth_labToZ {n:nat} (vls: Vector.t T n) (m:nat) : Z :=
  match le_lt_dec n m with
  | left _ => dontCare
  | right p => labToZ (Vector.nth_order vls p)
  end.

Lemma of_nat_lt_proof_irrel:
  forall (m n: nat) (p q: m < n),
    Fin.of_nat_lt p = Fin.of_nat_lt q.
Proof.
  induction m; intros.
    destruct n.
      omega.
      reflexivity.
    destruct n.
      omega.
      simpl; erewrite IHm; eauto.
Qed.

Lemma nth_order_proof_irrel:
  forall (m n: nat) (v: Vector.t T n) (p q: m < n),
    Vector.nth_order v p = Vector.nth_order v q.
Proof.
  intros.
  unfold Vector.nth_order.
  erewrite of_nat_lt_proof_irrel; eauto.
Qed.

Lemma nth_order_valid: forall (n:nat) (vls: Vector.t T n) m,
  forall (lt: m < n),
  nth_labToZ vls m = labToZ (Vector.nth_order vls lt).
Proof.
  intros.
  unfold nth_labToZ.
  destruct (le_lt_dec n m).
  omega.
  erewrite nth_order_proof_irrel; eauto.
Qed.

Definition labsToZs {n:nat} (vls :Vector.t T n) : (Z * Z * Z) :=
(nth_labToZ vls 0,
 nth_labToZ vls 1,
 nth_labToZ vls 2).

End Encodable.
