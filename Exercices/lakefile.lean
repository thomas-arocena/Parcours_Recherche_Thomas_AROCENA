import Lake
open Lake DSL

package «Projet» where
  -- add package configuration options here

lean_lib «Projet» where
  -- add library configuration options here


require LeanSearchClient from git "https://github.com/leanprover-community/LeanSearchClient" @ "v4.12.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

@[default_target]
lean_exe «projet» where
  root := `Main
