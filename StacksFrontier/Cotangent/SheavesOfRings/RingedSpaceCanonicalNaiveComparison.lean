module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RingedSpace.NaiveCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCanonical
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceNaiveComparison

/-!
# The canonical map of Tag 08UW

Let `f : X ⟶ S` be a morphism of ringed spaces. This file constructs the canonical map
`L_{X/S} ⟶ NL_{X/S}` from the cotangent complex of `f` (Definition 08UU) to its naive cotangent
complex `AlgebraicGeometry.RingedSpace.naiveCotangentComplex` (Tag 08TN), and proves that it
identifies `NL_{X/S}` with the truncation `τ_{≥ -1} L_{X/S}`.

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison`: the canonical map of Tag 08UW.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison_isIso_homologyMap` (**Tag 08UW**):
  the canonical map is an isomorphism on `Hⁱ` for every `i ≥ -1`, so it identifies `NL_{X/S}`
  with `τ_{≥ -1} L_{X/S}`.

## Implementation notes

Both are the special case at `f⁻¹𝒪_S ⟶ 𝒪_X` of `CategoryTheory.Sheaf.canonicalNaiveComparison`
and its theorem (Tag 08US), which read the comparison
`Stacks.Sheaves.RingedSpaceCotangent.naiveComparison` in the canonical naive cotangent complex
through the isomorphism `CategoryTheory.Sheaf.naiveCotangentComplexIsoCanonical` of the
presentation `P₀` with the polynomial presentation `f⁻¹𝒪_S[𝒪_X]`.

## References

* [Stacks Project, Tag 08UW](https://stacks.math.columbia.edu/tag/08UW)
* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US), the same comparison for
  a morphism of sheaves of rings on a site, of which Tag 08UW is a special case.
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN), the naive cotangent
  complex of a morphism of ringed spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Category CategoryTheory.Limits Opposite Simplicial
open TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageStructureMap)

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X S : RingedSpace.{u, u}}

/-- The canonical map `L_{X/S} ⟶ NL_{X/S}` from the cotangent complex of a morphism of ringed
spaces to its naive cotangent complex `AlgebraicGeometry.RingedSpace.naiveCotangentComplex`: the
canonical map `CategoryTheory.Sheaf.canonicalNaiveComparison` for the morphism of sheaves of
rings `f⁻¹𝒪_S ⟶ 𝒪_X`. -/
@[stacks 08UW "the canonical map `L_{X/Y} → NL_{X/Y}`, into the naive cotangent complex
`AlgebraicGeometry.RingedSpace.naiveCotangentComplex` of Tag 08TN; the special case of the map of
Tag 08US"]
noncomputable def canonicalNaiveComparison (f : X ⟶ S) :
    cotangentComplex f ⟶ RingedSpace.naiveCotangentComplex f :=
  CategoryTheory.Sheaf.canonicalNaiveComparison (Opens.grothendieckTopology X.carrier)
    (inverseImageStructureMap f)

/-- The canonical map `L_{X/S} ⟶ NL_{X/S}` is an isomorphism on the cohomology sheaf of every
degree `≥ -1`. Since `NL_{X/S}` has no terms outside degrees `-1` and `0`
(`AlgebraicGeometry.RingedSpace.naiveCotangentComplex_isZero_X`), the canonical map identifies
the naive cotangent complex with the truncation `τ_{≥ -1} L_{X/S}`. -/
@[stacks 08UW "the canonical map identifies the naive cotangent complex `NL_{X/Y}` with the
truncation `τ_{≥ -1} L_{X/Y}`: it is an isomorphism on the cohomology sheaf of every degree
`≥ -1`, the naive complex having no terms outside degrees `-1` and `0`; the special case of
Tag 08US"]
theorem canonicalNaiveComparison_isIso_homologyMap (f : X ⟶ S) (i : ℤ) (hi : -1 ≤ i) :
    IsIso (HomologicalComplex.homologyMap (canonicalNaiveComparison f) i) :=
  CategoryTheory.Sheaf.canonicalNaiveComparison_isIso_homologyMap
    (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f) i hi

end Stacks.Sheaves.RingedSpaceCotangent

end
