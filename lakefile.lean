import Lake
open Lake DSL

package "TacticLearning" where
  -- add package configuration options here
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib"

lean_lib «TacticLearning» where
  -- add library configuration options here

@[default_target]
lean_exe "tacticlearning" where
  root := `Main

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
