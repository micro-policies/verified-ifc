
(** * Assumptions and lemmas about the label structure. *)

(** Assumptions: labels form a join-semi-lattice. *)
Parameter Lab : Type.
Parameter bot : Lab.
Parameter join : Lab -> Lab -> Lab.
Parameter flows : Lab -> Lab -> Prop.

Notation "l1 \_/ l2" := (join l1 l2) (at level 40) : type_scope.
Notation "l1 <: l2" := (flows l1 l2) (at level 50, no associativity) : type_scope.

(* Might be used at some point as the default for clearance
Parameter top : Lab.
Hypothesis flows_top : forall l, l <: top. *)

Hypothesis bot_flows : forall l, bot <: l.
Hypothesis flows_refl : forall l, l <: l.
Hypothesis flows_trans : forall l1 l2 l3,
  l1 <: l2 -> l2 <: l3 -> l1 <: l3.
Hypothesis flows_antisymm : forall l1 l2,
  l1 <: l2 -> l2 <: l1 -> l1 = l2.
Hypothesis flows_join_right : forall l1 l2, l1 <: l1 \_/ l2.
Hypothesis flows_join_left : forall l1 l2, l2 <: l1 \_/ l2.
Hypothesis join_minimal : forall l1 l2 l,
  l1 <: l -> l2 <: l -> l1 \_/ l2 <: l.

Hypothesis flows_dec : forall l1 l2,
  {l1 <: l2} + {~l1 <: l2}.


(** Immediate properties from the semi-lattice structure. *)
Lemma join_1_rev : forall l1 l2 l,
  l1 \_/ l2 <: l -> l1 <: l.
Proof. eauto using flows_trans, flows_join_right. Qed.

Lemma join_2_rev : forall l1 l2 l,
  l1 \_/ l2 <: l -> l2 <: l.
Proof. eauto using flows_trans, flows_join_left. Qed.

Lemma join_1 : forall l l1 l2,
  l <: l1 -> l <: l1 \_/ l2.
Proof. eauto using flows_trans, flows_join_right. Qed.

Lemma join_2 : forall l l1 l2,
  l <: l2 -> l <: l1 \_/ l2.
Proof. eauto using flows_trans, flows_join_left. Qed.

Lemma join_bot : forall l,
  l \_/ bot = l.
Proof. intro l. symmetry. apply flows_antisymm.
  apply flows_join_right.
  apply join_minimal. apply flows_refl. apply bot_flows.
Qed.
