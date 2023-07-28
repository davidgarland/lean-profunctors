import Lake
open Lake DSL

package «profunctors» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Profunctors» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

