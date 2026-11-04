module

public import Mathlib.Algebra.Homology.ComplexShapeSigns
import StacksCore.Tactic.StacksAttribute

/-! ## Signs in the total complex

Stacks 012Z puts the sign `(-1)^p` on the vertical differential `d₂^{p, q}` of a double complex
when forming the total complex. Mathlib keeps such signs in a `TotalComplexShape c₁ c₂ c₁₂`: the
map `π` on indices together with two signs `ε₁`, `ε₂`. For a single shape `c` with `TensorSigns`
— in particular `up ℤ` — the instance `ComplexShape.instTotalComplexShape` sets `π (p, q) = p + q`,
`ε₁ = 1` and `ε₂ (p, q) = c.ε p`, and `ε_up_ℤ` says `(up ℤ).ε p = (-1)^p`; together these are the
tag's convention. The summand-wise formula itself is `HomologicalComplex₂.ιTotal_d_up_ℤ` in
`StacksCore.Algebra.Homology.TotalComplex`.
-/

@[expose] public section

add_to_stacks 012Z "the sign convention: `π (p, q) = p + q`, `ε₁ = 1`, `ε₂ (p, q) = c.ε p`"
  ComplexShape.instTotalComplexShape
add_to_stacks 012Z "the tag's sign `(-1)^p`, as `(up ℤ).ε p`" ComplexShape.ε_up_ℤ

add_to_stacks 08BI "the sign compatibility under which `Tot(Tot₁₂)` and `Tot(Tot₂₃)` agree"
  ComplexShape.Associative
