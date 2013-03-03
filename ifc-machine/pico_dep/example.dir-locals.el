((coq-mode . (
   ;; HACK: Include everything at two levels, so that relative paths
   ;; make sense when editing a file at either level.
   (coq-load-path . ("../lib" "../../lib"
                     "../common" "../../common"
                     "../tmu" "../../tmu"
                     "../tmu/amach" "../../tmu/amach"
                     "../tmu/cmach" "../../tmu/cmach"
                     "../tmu/amach_ni" "../../tmu/amach_ni")))))
