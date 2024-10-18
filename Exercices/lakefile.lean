import Lake
open Lake DSL

package «Projet» where
  -- add package configuration options here

lean_lib «Projet» where
  -- add library configuration options here

@[default_target]
lean_exe «projet» where
  root := `Main
