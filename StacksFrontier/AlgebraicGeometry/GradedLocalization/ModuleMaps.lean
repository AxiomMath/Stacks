module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction

/-!
# The action of the degrees of a graded ring on the degrees of a graded module

A graded module over an `ℕ`-graded ring is graded by `ℤ`, so `SetLike.GradedSMul` is applied
to index types `ℕ` and `ℤ` and needs a `VAdd ℕ ℤ` instance, which Mathlib does not provide.
This file supplies it as a scoped instance, so that a statement quantifying over a graded
module can name `SetLike.GradedSMul 𝒜 𝒨` without having to introduce the action itself.

## Main definitions

* `Stacks.GradedLocalization.instVAddNatInt`: the action `n +ᵥ i = n + i` of `ℕ` on `ℤ`.

## Implementation notes

The degree-zero localization `M_(f)` of a graded module, the restriction maps it carries along
an inclusion `D₊(g) ⊆ D₊(f)` of standard opens, and the corresponding maps of degree-zero rings
are `GradedModuleDegreeZeroLocalization`, `ProjectiveSpectrum.moduleRestrictionMaps`,
`ProjectiveSpectrum.localizedRingMap` and `ProjectiveSpectrum.degreeZeroRingMap`, all of which
live in `StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction` and the files it
imports. Those are the bearers of Tag 01M4; nothing here asserts anything about it. The
instance is deliberately scoped rather than global: it is a choice of action, and the files
that use it say so by opening this namespace.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public section

namespace Stacks.GradedLocalization

/-- The grading action used for a naturally graded ring acting on an integer-graded module. -/
scoped instance instVAddNatInt : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

end Stacks.GradedLocalization

end
