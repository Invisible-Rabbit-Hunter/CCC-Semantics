import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"


package «cCC-Semantics» {
  -- add package configuration options here
}

lean_lib «CCCSemantics» {
  -- add library configuration options here
}

@[default_target]
lean_exe «cCC-Semantics» {
  root := `Main
}
