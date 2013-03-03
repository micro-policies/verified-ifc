#!/bin/bash

function all_modules {
    echo -n "import qualified Prelude";
    for mod in Data.Bits; do
        echo -n "\nimport qualified ${mod}"
    done
}

for f in $(grep -l 'import qualified Prelude' *.hs); do
    # avoid mac os haskell bug
    perl -pi -e 's/unsafeCoerce :: a -> b//' $f;

    # import more modules
    perl -pi -e "s/import qualified Prelude/$(all_modules)/" $f;
done
