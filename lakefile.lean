import Lake
open Lake DSL

package «final-project» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require aesop from git
  "https://github.com/leanprover-community/aesop"

@[default_target]
lean_lib «FinalProject» {
  -- add library configuration options here
}
