Require Import ZArith.
Require Import List.

Require Import Instr.
Require Import CodeSpecs.
Require Import CodeTriples.
Require Import Concrete.
Require Import Encodable.
Require Import Utils.

Definition listify_apply_rule {T} `{Encodable T} (ar: option (T * T)) (s0: stack): stack :=
  match ar with
  | None            => CData (0, handlerTag) :: s0
  | Some (lrpc, lr) => CData (1, handlerTag) ::
                        CData (labToZ lr, handlerTag) ::
                        CData (labToZ lrpc, handlerTag) :: s0
  end.

Definition handler_initial_mem_matches
           (opcode: Z) (tags : Z * Z * Z)
           (pctag: Z)
           (m: memory) : Prop :=
  let '(tag1,tag2,tag3) := tags in
     index_list_Z addrOpLabel m = Some (opcode,handlerTag)
  /\ index_list_Z addrTag1 m = Some (tag1,handlerTag)
  /\ index_list_Z addrTag2 m = Some (tag2,handlerTag)
  /\ index_list_Z addrTag3 m = Some (tag3,handlerTag)
  /\ index_list_Z addrTagPC m = Some (pctag,handlerTag).

Class ConcreteLabels (L : Type)
                     (EL : Encodable L)
                     (labelCount : OpCode -> nat)
                     (run_tmr : forall opcode,
                                  L ->
                                  Vector.t L (labelCount opcode) ->
                                  option (L * L)) := {

  genRule : OpCode -> list Instr;

  genRuleCorrect :
    forall opcode m0 (labs : Vector.t L (labelCount opcode)) pcl (Q : memory -> stack -> Prop),
      handler_initial_mem_matches (opCodeToZ opcode) (labsToZs labs) (labToZ pcl) m0 ->
      HT (genRule opcode)
         (fun m s =>
            m = m0 /\
            Q m (listify_apply_rule (run_tmr opcode pcl labs) s))
         Q

}.
