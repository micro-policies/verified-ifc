module Driver where

import LatticeHL
import TMUInstr
import TMURules
import Datatypes
import TMUAbstract 

instance Show Lab where
   show L = "L"
   show H = "H"

instance (Show a, Show b) => Show (Coq_sum a b)  where 
   show (Coq_inr r) = show r
   show (Coq_inl l) = show l

instance (Show a) => Show (RVector a) where
   show rv = "{ labres="++ show (rv_labRes rv)
             ++"; labPC="++ show (rv_labResPC rv)
             ++"}"

instance (Show a) => Show (AS a) where
    show s = "AS"

main = 
    print (run_tmm_example state1)
