import Lake
open Lake DSL

package leanhello {
  -- add package configuration options here
}

lean_lib Leanhello {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe leanhello {
  root := `Main
}
