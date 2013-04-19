Require Monad.
Require TMUInstr.
Require LatticeHL.
Require Rules.
Require AbstractMachineFun.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Extraction Language Haskell.

Extract Inductive unit => "()" [ "()" ].

Extract Inductive comparison => "Prelude.Ordering"
  [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ]
  "(\ feq flt fgt c -> case c of
      Prelude.EQ -> feq ()
      Prelude.LT -> flt ()
      Prelude.GT -> fgt () )".

Extract Inductive nat => "Prelude.Integer"
  [ "0" "Prelude.succ" ]
  "(\ f0 fs n ->
      if (Prelude.==) n 0 then f0 () else fs ((Prelude.-) n 1))".

Extract Inductive bool => "Prelude.Bool"
  [ "Prelude.True" "Prelude.False" ]
  "(\ ft ff b -> if b then ft () else ff ())".

Extract Inductive sumbool => "Prelude.Bool"
  [ "Prelude.True" "Prelude.False" ]
  "(\ ft ff b -> if b then ft () else ff ())".

Extract Inductive prod => "(,)"
  [ "(,)" ]
  "(\ f p -> f (Prelude.fst p) (Prelude.snd p))".

Extract Inductive list => "[]"
  [ "[]" "(:)" ]
  "(\ fnil fcons l -> case l of { [] -> fnil (); (a:as) -> fcons a as; })".

Extract Inductive option => "Prelude.Maybe"
  [ "Prelude.Just" "Prelude.Nothing" ]
  "(\ fj fn e -> case e of {
                   Prelude.Just a -> fj a;
                   Prelude.Nothing -> fn (); })".


Cd "extraction".
Recursive Extraction Library Monad.
Recursive Extraction Library LatticeHL.
Recursive Extraction Library TMUInstr.
Recursive Extraction Library Rules.
Recursive Extraction Library AbstractMachineFun.
