import Lake
open Lake DSL

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
