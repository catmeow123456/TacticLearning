import Lake
open Lake DSL

package "TacticLearning" where
  -- add package configuration options here

require "leanprover-community" / "mathlib"

lean_lib «TacticLearning» where
  -- add library configuration options here

@[default_target]
lean_exe "tacticlearning" where
  root := `Main
