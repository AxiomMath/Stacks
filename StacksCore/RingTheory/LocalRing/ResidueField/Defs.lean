module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import StacksCore.Tactic.StacksAttribute

/-! # The residue field of a local ring

Stacks tag 07BI, third sentence: the residue field `κ = R/𝔪_R` of a local ring `R`, and the
quotient map onto it. Mathlib has both, as `IsLocalRing.ResidueField` and
`IsLocalRing.residue`. The Stacks project writes `(R, 𝔪, κ)` for the package; in Lean the
three are recovered from the single instance `IsLocalRing R`.
-/

@[expose] public section

add_to_stacks 07BI "The residue field `κ = R/𝔪_R` of a local ring." IsLocalRing.ResidueField
add_to_stacks 07BI "The quotient map `R → R/𝔪_R = κ` onto the residue field."
  IsLocalRing.residue
