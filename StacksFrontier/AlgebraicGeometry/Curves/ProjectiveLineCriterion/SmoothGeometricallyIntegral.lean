module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveLineCharacterization
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.SmoothAffineGeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Smooth schemes over a field: geometric integrality and the Gorenstein property

The reductions "(2) ⟹ (3)" and "(3) ⟹ (4)" in the proof of [Stacks, Tag 0C6U], in the forms the
assembly consumes.

* A scheme smooth over `k` is regular ([Stacks, Tag 056S]), hence Gorenstein
  ([Stacks, Tag 0DWG]).
* A smooth, geometrically irreducible scheme over `k` is geometrically integral: smoothness gives
  geometric reducedness ([Stacks, Tag 056T]).
* A proper smooth scheme over `k` with `H⁰(X, 𝒪_X) = k` is geometrically irreducible and
  geometrically integral ([Stacks, Tag 0FD3], a smooth scheme being geometrically normal).
* Conversely a proper geometrically integral scheme has `H⁰(X, 𝒪_X) = k` ([Stacks, Tag 04L2]);
  this is `AlgebraicGeometry.isIso_globalSections_of_geometricallyIntegral` on the base, and is
  not restated here.

## Main results

* `AlgebraicGeometry.ProjectiveLineCriterion.isGorenstein_of_smooth`
* `AlgebraicGeometry.ProjectiveLineCriterion.geometricallyIrreducible_of_smooth_of_isIso`
* `AlgebraicGeometry.ProjectiveLineCriterion.geometricallyIntegral_of_smooth_of_isIso`

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 0DWG](https://stacks.math.columbia.edu/tag/0DWG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveLineCriterion

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A scheme smooth over a field is Gorenstein**: it is regular ([Stacks, Tag 056S]) and a
regular scheme is Gorenstein ([Stacks, Tag 0DWG]). -/
theorem isGorenstein_of_smooth [Smooth f] : IsGorenstein X :=
  isGorenstein_of_isRegular X (isRegular_of_smooth_over_field f)

/-- A proper smooth scheme over `k` with `H⁰(X, 𝒪_X) = k` is geometrically irreducible and
geometrically integral. -/
private theorem geometricallyIrreducible_and_integral_of_smooth_of_isIso [IsProper f] [Smooth f]
    [h : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    GeometricallyIrreducible f ∧ GeometricallyIntegral f :=
  have tfae := isIso_globalSections_tfae_geometricallyConnected_irreducible_integral k f
    (isGeometricallyNormal_of_smooth f)
  ⟨(tfae.out 1 3).mp h, (tfae.out 1 4).mp h⟩

/-- **A proper smooth scheme over `k` with `H⁰(X, 𝒪_X) = k` is geometrically irreducible**
([Stacks, Tag 0FD3]). -/
theorem geometricallyIrreducible_of_smooth_of_isIso [IsProper f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] : GeometricallyIrreducible f :=
  (geometricallyIrreducible_and_integral_of_smooth_of_isIso f).1

/-- **A proper smooth scheme over `k` with `H⁰(X, 𝒪_X) = k` is geometrically integral**
([Stacks, Tag 0FD3]). -/
theorem geometricallyIntegral_of_smooth_of_isIso [IsProper f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] : GeometricallyIntegral f :=
  (geometricallyIrreducible_and_integral_of_smooth_of_isIso f).2

end AlgebraicGeometry.ProjectiveLineCriterion

end
