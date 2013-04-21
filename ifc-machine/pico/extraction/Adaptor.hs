module Adaptor where

import Abstract
import qualified Lattices as L
import LatticeHL

class JoinSemiLattice l where
  bot :: l
  join :: l -> l -> l
  flows :: l -> l -> Bool

instance JoinSemiLattice Lab where
  bot = L.bot coq_HL
  join = L.join coq_HL
  flows = L.flows coq_HL

instance Show Lab where
   show L = "L"
   show H = "H"

instance (Show a) => Show (AS a) where
    show s = "AS"
