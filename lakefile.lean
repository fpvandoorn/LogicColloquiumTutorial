import Lake
open Lake DSL

def moreLeanArgs := #[
  "-Dpp.unicode.fun=true" -- pretty-prints `fun a ↦ b`
]

def moreServerArgs := moreLeanArgs

package LCTutorial where
  moreLeanArgs := moreLeanArgs
  moreServerArgs := moreServerArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LCTutorial where
  moreLeanArgs := moreLeanArgs
