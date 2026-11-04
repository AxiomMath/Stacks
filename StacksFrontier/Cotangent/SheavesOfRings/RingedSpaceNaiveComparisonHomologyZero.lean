module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCanonical
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceNaiveComparison

/-!
# The canonical map `L_{X/S} ⟶ NL_{X/S}` on degree-zero cohomology

For a morphism of ringed spaces `f : X ⟶ S`, the canonical map
`Stacks.Sheaves.RingedSpaceCotangent.naiveComparison` from the cotangent complex to the naive
cotangent complex is an isomorphism on the degree-zero cohomology sheaf, both sides being
`Ω_{X/S}`.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.isIso_homologyMap_naiveComparison_zero`: the canonical map
  `L_{X/S} ⟶ NL_{X/S}` is an isomorphism on the degree-zero cohomology sheaf.

## References

* [Stacks Project, Tag 08UW](https://stacks.math.columbia.edu/tag/08UW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageStructureMap)

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X S : RingedSpace.{u, u}}

/-- The canonical map `L_{X/S} ⟶ NL_{X/S}` is an isomorphism on the degree-zero cohomology
sheaf, both sides being the sheaf of relative differentials `Ω_{X/S}`. -/
@[stacks 08UW "the degree-zero clause of the second assertion: the canonical map
`L_{X/Y} → NL_{X/Y}` is an isomorphism on the degree-zero cohomology sheaf, both sides being
`Omega_{X/Y}`. `NL_{X/Y}` is realized as the two-term complex of the conormal sequence of the
presentation `P₀ ⟶ O_X` by the degree-zero term of the standard resolution, as for
`Stacks.Sheaves.RingedSpaceCotangent.naiveComparison`"]
theorem isIso_homologyMap_naiveComparison_zero (f : X ⟶ S) :
    IsIso (HomologicalComplex.homologyMap (naiveComparison f) 0) :=
  CategoryTheory.Sheaf.naiveComparison_isIso_homologyMap_zero
    (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f)

end Stacks.Sheaves.RingedSpaceCotangent

end
