Require Import List.

Require Import Utils.
Require Import Lattices.
Require Import Abstract.
Require Import Rules.
Require AbstractMachine.
Require QuasiAbstractMachine.
Require Import Ref.
Require Import TINI.

Section Refinement.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Lemma step_rules_equiv : forall s e s',
                           QuasiAbstractMachine.step_rules s e s' <->
                           AbstractMachine.step_rules s e s'.
Proof.
  intros.
  split; intro H; inv H;
  unfold QuasiAbstractMachine.run_tmr, apply_rule in *;
  simpl in *;
  repeat match goal with
           | H : Some _ = Some _ |- _ =>
             inv H
           | H : (if ?b then _ else _) = _ |- _ =>
             destruct b eqn:E; inv H
         end;
  unfold Vector.nth_order in *; simpl in *;
  try econstructor (solve [compute; eauto]).

  econstructor; eauto.
  unfold QuasiAbstractMachine.run_tmr, apply_rule. simpl.
  unfold Vector.nth_order. simpl.
  rewrite H2. trivial.
Qed.

Lemma abstract_quasi_abstract_bwdsim :
  backward_simulation AbstractMachine.step_rules
                      QuasiAbstractMachine.step_rules
                      eq eq (fun x => x) (fun x => x).
Proof.
  apply strong_backward_simulation.
  intros until 1. subst.
  rewrite step_rules_equiv.
  eauto.
Qed.

End Refinement.
