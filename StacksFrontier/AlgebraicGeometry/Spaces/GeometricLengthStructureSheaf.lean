module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# The length of the structure sheaf at a geometric point

Let `X` be an algebraic space over a scheme `S` and let `x̄` be a geometric point of `X`. The
length of Stacks 0EE1 at `x̄` of the structure sheaf, that is of the free `𝒪_X`-module of rank
one, is the length of the étale local ring `𝒪_{X, x̄}` as a module over itself.

This is the bridge between the two sides of every multiplicity computation on an algebraic
space. On one side the multiplicity of an integral closed subspace in the fundamental cycle of
a closed subspace is `AlgebraicGeometry.Space.geometricLength` of a structure sheaf, through
`AlgebraicGeometry.Space.closedSubspaceMultiplicity` and
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`. On the other side every computation of
such a length is a computation about `𝒪_{X, x̄}` or about the local ring of an étale scheme
chart — `AlgebraicGeometry.Space.length_etaleLocalRing_eq_length_chartLocalRing`, which is the
case of the structure sheaf of Stacks 0EE1, and the colength formulas for an invertible ideal.
Nothing identified the two: the geometric stalk is an extension of scalars along
`AlgebraicGeometry.Space.pointStalkRingEquiv` of the stalk at the point of the small étale
site, so the identity is not a definitional unfolding and `rfl` does not prove it.

## Main results

* `AlgebraicGeometry.Space.geometricLength_unit_eq_length_etaleLocalRing`: **the length of
  `𝒪_X` at `x̄` is the length of `𝒪_{X, x̄}` over itself.**
* `AlgebraicGeometry.Space.geometricLength_unit_eq_length_chartLocalRing`: the same length read
  on an étale scheme chart, by Stacks 0EE1 for the structure sheaf.

## Implementation notes

No declaration here carries a tag. Stacks 0EE1 is already carried by
`AlgebraicGeometry.Space.length_etaleLocalRing_eq_length_chartLocalRing` and by the
independence results of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricLengthPointIndependence.lean`; what is added
here is the identification of the quantity those results compute with the length that
`AlgebraicGeometry.Space.geometricLength` assigns to the structure sheaf, which is an auxiliary
bridge and not a statement of the source.

The content is entirely in
`AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv`, which crosses the extension of
scalars separating the stalk at the point of the small étale site from the geometric stalk.
That equivalence is stated for `AlgebraicGeometry.Space.structureSheafModule`, the abbreviation
for `SheafOfModules.unit` of the sheaf of rings of the small étale ringed site; the statements
below are written with `SheafOfModules.unit` directly, which is the spelling the consumers use,
and the two agree because the abbreviation is reducible.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)

/-- **The length of the structure sheaf at a geometric point is the length of the étale local
ring over itself.** For an algebraic space `X` and a geometric point `x̄` of it, the length of
Stacks 0EE1 of `𝒪_X` at `x̄` — the length over `𝒪_{X, x̄}` of the stalk of Stacks 05VQ — is the
length of `𝒪_{X, x̄}` as a module over itself.

The stalk of `𝒪_X` at `x̄` is `𝒪_{X, x̄}` as a module over itself
(`AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv`), and a linear equivalence
preserves length. -/
theorem geometricLength_unit_eq_length_etaleLocalRing :
    geometricLength B S hS X x (SheafOfModules.unit _) =
      Module.length ↥(etaleLocalRing B S hS X.1 x) ↥(etaleLocalRing B S hS X.1 x) :=
  LinearEquiv.length_eq (structureSheafGeometricStalkEquiv B S hS X x)

/-- **The length of the structure sheaf at a geometric point, read on an étale scheme chart.**
It is the length over `𝒪_{U, u}` of `𝒪_{U, u}` itself, for any small étale neighbourhood `U` of
`x̄` whose chart is a scheme and any point `u` of it under the chosen lift of `x̄`.

This is `AlgebraicGeometry.Space.geometricLength_unit_eq_length_etaleLocalRing` followed by
`AlgebraicGeometry.Space.length_etaleLocalRing_eq_length_chartLocalRing`, the case of the
structure sheaf of Stacks 0EE1. -/
theorem geometricLength_unit_eq_length_chartLocalRing (V : SmallEtaleNeighborhood x) :
    geometricLength B S hS X x (SheafOfModules.unit _) =
      Module.length ↥(chartLocalRing B S hS X.1 V) ↥(chartLocalRing B S hS X.1 V) :=
  (geometricLength_unit_eq_length_etaleLocalRing B S hS X x).trans
    (length_etaleLocalRing_eq_length_chartLocalRing B S hS X.1 X.2 V)

end AlgebraicGeometry.Space

end
