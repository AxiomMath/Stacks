module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor

/-!
# Derived equivalence of schemes over a field

Two schemes over a field `k` are derived equivalent when their categories of perfect
complexes are equivalent by a `k`-linear exact equivalence. The notion is used for smooth
projective schemes, but neither smoothness nor projectivity enters the definition.

## Main definitions

* `AlgebraicGeometry.DerivedEquivalent` is derived equivalence of two schemes over a field.

## Implementation notes

The category of perfect complexes is
`Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`, the full subcategory of
the derived category of sheaves of modules spanned by the perfect objects. An exact
equivalence is an equivalence whose functor commutes with the shift and preserves
distinguished triangles. The `k`-action on modules comes from the structure morphism to
`Spec k` through `AlgebraicGeometry.modulesLinear`, and is supplied explicitly because it
depends on that morphism. The definition is an abbreviation, so that a client can use its
existential form directly.

## References

* [Stacks Project, Tag 0G10](https://stacks.math.columbia.edu/tag/0G10)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Two schemes over a field `k` are *derived equivalent* if their categories of perfect
complexes admit a `k`-linear exact equivalence. -/
@[stacks 0G10]
abbrev DerivedEquivalent (k : Type u) [Field k] (X Y : Over (Spec (.of k))) : Prop :=
  letI : Linear k X.left.Modules := modulesLinear k X
  letI : Linear k Y.left.Modules := modulesLinear k Y
  letI : Linear k (DerivedCategory X.left.Modules) := inferInstance
  letI : Linear k (DerivedCategory Y.left.Modules) := inferInstance
  ∃ e : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X.left ≌
      Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory Y.left,
    e.functor.Linear k ∧
      ∃ h : e.functor.CommShift ℤ,
        letI := h
        e.functor.IsTriangulated

end AlgebraicGeometry

end
