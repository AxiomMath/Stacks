module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.OneStepReduction

/-!
# Comparison of the two encodings of perfectness and of perfect approximation

Perfectness of a complex of `𝒪_X`-modules and of an object of the derived category is defined
twice, once at coinciding space, ring and module universes and once at an independent module
universe; the two definitions agree where both are defined. The same holds for the perfect
approximation condition on a triple `(T, E, m)` and for approximation by perfect complexes on a
scheme.

## Main results

* `Stacks.Cohomology.PerfectComplexes.isPerfectComplex_iff_ringedSpace` and
  `Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace`: the two perfectness
  predicates agree.
* `AlgebraicGeometry.PerfectApproximation.approximationHolds_iff_hasPerfectApproximation`:
  the two perfect approximation conditions on a triple `(T, E, m)` agree.
* `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_iff`: the two
  definitions of approximation by perfect complexes on a scheme agree.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08EN](https://stacks.math.columbia.edu/tag/08EN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace Stacks.Cohomology.PerfectComplexes

universe u d

/-- The two spellings of perfectness of a complex of `𝒪_X`-modules agree at coinciding space,
ring and module universes. -/
theorem isPerfectComplex_iff_ringedSpace {X : RingedSpace.{u, u}}
    (E : CochainComplex (OXMod.{u, u, u} X) ℤ) :
    IsPerfectComplex E ↔ RingedSpace.IsPerfectComplex E :=
  Iff.rfl

/-- The two spellings of perfectness of an object of the derived category of `𝒪_X`-modules
agree at coinciding space, ring and module universes. -/
theorem isPerfect_iff_ringedSpace {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u, u} X)]
    (K : DerivedCategory (OXMod.{u, u, u} X)) :
    IsPerfect K ↔ RingedSpace.IsPerfect K :=
  Iff.rfl

end Stacks.Cohomology.PerfectComplexes

namespace AlgebraicGeometry.PerfectApproximation

universe u

attribute [local instance] HasDerivedCategory.standard

/-- `ApproximationHolds` and `HasPerfectApproximation` agree on a triple `(T, E, m)`. -/
theorem approximationHolds_iff_hasPerfectApproximation (X : Scheme.{u}) (T : Set X)
    (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ) :
    ApproximationHolds X T E m ↔ HasPerfectApproximation X T E m :=
  Iff.rfl

/-- `ApproximationByPerfectComplexes` and `HasApproximationByPerfectComplexes` agree on a
scheme. -/
theorem approximationByPerfectComplexes_iff (X : Scheme.{u}) :
    ApproximationByPerfectComplexes X ↔ HasApproximationByPerfectComplexes X :=
  Iff.rfl

end AlgebraicGeometry.PerfectApproximation

end
