Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.

Require Import TMUInstr.
Require Import Abstract.
Require Import Rules.
Require Import AbstractMachine.

Require Vector.

Local Open Scope Z_scope.

Section Def.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Definition exec_instr (instr : @Instr T) (st : @AS T) : option (@AS T) :=
  let '(AState m i s (pcv, pcl)) := st in
  match instr with
    | Noop =>
      match run_tmr OpNoop <||> pcl with
        | Some (_, rpcl) => Some (upd_apc (pcv + 1, rpcl) st)
        | None => None
      end
    | Add =>
      match s with
        | AData (x1v, x1l) :: AData (x2v, x2l) :: s' =>
          match run_tmr OpSub <|x1l;x2l|> pcl with
            | Some (Some rl, rpcl) => Some (AState m i (AData (x1v+x2v,rl)::s') (pcv+1,rpcl))
            | _ => None
          end
        | _ => None
      end
    | Sub =>
      match s with
        | AData (x1v, x1l) :: AData (x2v, x2l) :: s' =>
          match run_tmr OpAdd <|x1l;x2l|> pcl with
            | Some (Some rl, rpcl) => Some (AState m i (AData (x1v-x2v,rl)::s') (pcv+1,rpcl))
            | _ => None
          end
        | _ => None
      end
    | Push (cv,cl) =>
      match run_tmr OpPush <|cl|> pcl with
        | Some (Some rl, rpcl) =>
          Some (AState m i (AData (cv,rl)::s) (pcv+1,rpcl))
        | _ => None
      end
    | Load =>
      match s with
        | AData (addrv,addrl)::s' =>
          match index_list_Z addrv m with
            | Some (xv,xl) =>
              match run_tmr OpLoad <|addrl;xl|> pcl with
                | Some (Some rl, rpcl) =>
                  Some (AState m i (AData (xv,rl)::s') (pcv+1,rpcl))
                | _ => None
              end
            | None => None
          end
        | _ => None
      end
    | Store =>
      match s with
        | AData (addrv,addrl)::AData (xv,xl)::s' =>
          match index_list_Z addrv m with
            | Some (mv,ml) =>
              match run_tmr OpStore <|addrl;xl;ml|> pcl with
                | Some (Some rl, rpcl) =>
                  match update_list_Z addrv (xv,rl) m with
                    | Some m' =>
                      Some (AState m' i s' (pcv+1,rpcl))
                    | None => None
                  end
                | _ => None
              end
            | None => None
          end
        | _ => None
      end
    | Jump =>
      match s with
        | AData (pcv',pcl') :: s' =>
          match run_tmr OpJump <|pcl'|> pcl with
            | Some (_, rpcl) =>
              Some (AState m i s' (pcv',rpcl))
            | None => None
          end
        | _ => None
      end
    | BranchNZ offv =>
      match s with
        | AData (av,al) :: s' =>
          match run_tmr OpBranchNZ <|al|> pcl with
            | Some (_, rpcl) =>
              let pcv' :=
                  match av with
                    | 0 => pcv+1
                    | _ => pcv+offv
                  end in
              Some (AState m i s' (pcv',rpcl))
            | None => None
          end
        | _ => None
      end
    | Call n b => None
    | Ret => None
    | VRet => None
    | Halt => None
  end.

Definition stepF (st : @AS T) : option (@AS T) :=
  match index_list_Z (fst (apc st)) (aimem st) with
    | Some i => exec_instr i st
    | None => None
  end.

Hint Unfold upd_apc.
Hint Constructors step_rules.

Ltac match_inversion :=
  repeat (try congruence;
          match goal with
           | H : Some _ = Some _ |- _ =>
             inversion H; subst; clear H
           | H : match ?t with
                   | nil => _
                   | _ :: _ => _
                 end = Some _ |- _ =>
             destruct t; inversion H; subst; clear H
           | H : match ?t with
                   | AData _ => _
                   | ARet _ _ => _
                 end = Some _ |- _ =>
             destruct t; inversion H; subst; clear H
           | H : match ?t with
                   | (_, _) => _
                 end = Some _ |- _ =>
             destruct t
           | H : match ?t with
                   | Some _ => _
                   | _ => _
                 end = Some _ |- _ =>
             let E := fresh "E" in
             destruct t eqn:E; try solve [inversion H]
         end; simpl in *; try congruence).

Theorem stepF_step_rules :
  forall st st',
    stepF st = Some st' ->
    step_rules st st'.
Proof.
  unfold stepF, exec_instr.
  intros [m is s [pcv pcl]] st' H. simpl in *.
  match_inversion.
  destruct i; simpl; match_inversion.
  eapply step_nop; eauto; try reflexivity.
  eapply step_add; eauto; try reflexivity.
  eapply step_sub; eauto; try reflexivity.
  eapply step_push; eauto; try reflexivity.
  eapply step_load; eauto; try reflexivity.
  eapply step_store; eauto; try reflexivity.
  eapply step_jump; eauto; try reflexivity.
  destruct z0.
    eapply step_branchnz_true; eauto; try reflexivity.
    eapply step_branchnz_false; eauto; try reflexivity. congruence.
    eapply step_branchnz_false; eauto; try reflexivity. congruence.
Qed.

End Def.
