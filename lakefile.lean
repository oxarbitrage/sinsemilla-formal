import Lake
open Lake DSL

package SinsemillaFormal where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Sinsemilla where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require pasta_formal from git
  "https://github.com/oxarbitrage/pasta-formal"
