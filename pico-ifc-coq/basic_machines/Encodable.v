Require Import ZArith.
Require Import Lattices.
Require Import CodeGen.

Open Scope Z_scope.

Class Encodable (L : Type) := {
  labToZ : L -> Z;
  ZToLab : Z -> L;
  ZToLab_labToZ_id : forall l, l = ZToLab (labToZ l)
}.

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

Lemma labToZ_inj: forall {L} {W: Encodable L} (l1 l2: L),
  labToZ l1 = labToZ l2 -> l1 = l2.
Proof.
  intros.
  rewrite (ZToLab_labToZ_id l1).
  rewrite (ZToLab_labToZ_id l2).
  apply f_equal; auto.
Qed.
