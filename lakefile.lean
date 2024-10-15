import Lake
open Lake DSL

package «HoTT_Model» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "30c481f1821c2b61dad5571b81b0bff368769ab5"

@[default_target]
lean_lib «HoTTModel» where
  -- add any library configuration options here
