import Lake
open Lake DSL

package N_Rubiks_Cube where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0-rc2"


@[default_target]
lean_lib «NRubiksCube» where
  -- add any library configuration options here
