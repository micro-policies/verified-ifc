import qualified Lattices
import qualified LatticeHL

class JoinSemiLattice l where
  bot :: l
  join :: l -> l -> l
  flows :: l -> l -> Bool

instance JoinSemiLattice LatticeHL.Lab where
  bot = Lattices.bot LatticeHL.coq_HL
  join = Lattices.join LatticeHL.coq_HL
  flows = Lattices.flows LatticeHL.coq_HL
