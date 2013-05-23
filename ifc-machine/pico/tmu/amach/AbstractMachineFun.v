Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.

Require Import TMUInstr.
Require Import Abstract.
Require Import Rules.
Require Import AbstractMachine.
Require Import AbstractCommon.
Require Import QuasiAbstractMachine.

Require Vector.

Local Open Scope Z_scope.

Section Def.

Context {T: Type}
        {Latt: JoinSemiLattice T}.
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

Fixpoint take_data (n : nat) (s : list (@StkElmt T)) : option (list (@StkElmt T) * list (@StkElmt T)) :=
  match n, s with
    | O, _ => Some (nil, s)
    | S n', AData a :: s' =>
      match take_data n' s' with
        | Some (atms, s'') => Some (AData a :: atms, s'')
        | None => None
      end
    | _, _ => None
  end.

Theorem take_data_spec : forall n s s1 s2,
                           take_data n s = Some (s1, s2) ->
                           length s1 = n /\
                           s = s1 ++ s2 /\
                           forall a, In a s1 -> exists d, a = AData d.
Proof.
  intros n.
  induction n as [|n]; simpl in *; intros s s1 s2 H;
  inversion H; subst; clear H.
  - repeat split; auto.
    intros a H. inversion H.
  - match_inversion.
    apply IHn in E. clear IHn.
    destruct E as [H1 [H2 H3]]; subst.
    repeat split; auto.
    intros a' []; eauto.
Qed.

Fixpoint pop_to_returnF (s : list (@StkElmt T)) :
  option (Z *  T * bool * list (@StkElmt T)) :=
  match s with
    | nil => None
    | AData _ :: s' => pop_to_returnF s'
    | ARet (pcv, pcl) b :: s' =>
      Some (pcv, pcl, b, s')
  end.

Theorem pop_to_returnF_spec :
  forall s pcv pcl b s',
    pop_to_returnF s = Some (pcv, pcl, b, s') ->
    pop_to_return s (ARet (pcv, pcl) b :: s').
Proof.
  intros s.
  induction s; intros pcv pcl b s' H.
  - inversion H.
  - destruct a as [a | [pcv' pcl'] b']; simpl in H.
    + apply IHs in H. econstructor. auto.
    + inversion H; subst. constructor.
Qed.

Definition exec_instr (instr : Instr) (st : @AS T) : option (@AS T) :=
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
    | Push cv =>
      match run_tmr OpPush <||> pcl with
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
    | Call a r =>
      match s with
        | AData (pcv',pcl') :: s' =>
          match run_tmr OpCall <|pcl'|> pcl with
            | Some (Some rl,rpcl) =>
              match take_data a s' with
                | Some (s1, s2) =>
                  Some (AState m i (s1 ++ ARet (pcv+1,rl) r :: s2) (pcv',rpcl))
                | None => None
              end
            | _ => None
          end
        | _ => None
      end
    | Ret =>
      match pop_to_returnF s with
        | Some (pcv', pcl', false, s') =>
          match run_tmr OpRet <|pcl'|> pcl with
            | Some (_,rpcl) =>
              Some (AState m i s' (pcv',rpcl))
            | None => None
          end
        | _ => None
      end
    | VRet =>
      match s with
        | AData (resv,resl) :: s' =>
          match pop_to_returnF s' with
            | Some (pcv',pcl',true,s'') =>
              match run_tmr OpVRet <|resl;pcl'|> pcl with
                | Some (Some rl, rpcl) =>
                  Some (AState m i (AData (resv,rl)::s'') (pcv',rpcl))
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end
    | Halt => None
    | Output => None (* DD: Arthur, I don't want to mess with your code... *)
  end.

Definition stepF (st : @AS T) : option (@AS T) :=
  match index_list_Z (fst (apc st)) (aimem st) with
    | Some i => exec_instr i st
    | None => None
  end.

Hint Unfold upd_apc.
Hint Constructors step_rules.


Theorem stepF_step_rules :
  forall st st',
    stepF st = Some st' ->
    exists e, step_rules st e st'.
Proof.
  unfold stepF, exec_instr.
  intros [m is s [pcv pcl]] st' H. simpl in *.
  match_inversion.
  destruct i; simpl; match_inversion;
    try (eexists ; econstructor (solve[ eauto; reflexivity])).
  destruct z0;
    try (eexists ; econstructor (solve[eauto; try reflexivity; congruence])).
  - apply take_data_spec in E0.
    destruct E0 as [H1 [H2 H3]]. subst.
    eexists ; econstructor ( solve [eauto; reflexivity]).
  - destruct b. inversion H.
    inv H.
    apply pop_to_returnF_spec in E0.
    eexists;  econstructor (solve [eauto; reflexivity]).
  - destruct b; inv H0.
    apply pop_to_returnF_spec in E0.
    econstructor (solve [eauto; reflexivity]).
Qed.

End Def.
