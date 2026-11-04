module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.SaturationFromRetractModels
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# `D_perf(O_X)` is a saturated subcategory of `D(O_X)`

Tag 0F8I asks for `D_perf(O_X)` as the strictly full, *saturated*, triangulated subcategory of
`D(O_X)` on the perfect objects.  Strict fullness is
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isClosedUnderIsomorphisms` and
triangulatedness is
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isTriangulated`; saturation —
closure under direct summands — is proved here.

Saturation is [Stacks, Tag 08CS], and this repository proves that tag unconditionally:
`Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`, through the characterisation of
[Stacks, Tag 08CQ] of the perfect objects as the pseudo-coherent ones of locally finite Tor
dimension.  So the clause costs one application and carries no hypothesis beyond the scheme.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.isSaturated_isPerfect`: on a ringed space,
  perfectness of an object of `D(O_X)` is a saturated property.  On a scheme this is the
  saturation clause of Tag 0F8I; the scheme-level statement is
  `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isSaturated`.

## Implementation notes

Saturation is deduced from the universe-polymorphic reduction
`Stacks.Perfect.BoundedLocallyFreeComplexes.isSaturated_isPerfect_of_biprod` of saturation to the
conclusion of Tag 08CS.

Tag 08CS is read at a module universe equal to the space universe, which is the generality of the
Tag 08CQ development behind it, and is no restriction for the scheme-level statement:
`X.toRingedSpace` is a `RingedSpace.{u, u}` and `X.Modules` is definitionally
`StrictlyPerfect.OXMod.{u, u}` of it.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes

universe u d

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-- **Perfectness is a saturated property of objects of `D(O_X)` on a ringed space.**  Both
summands of a perfect biproduct are perfect by [Stacks, Tag 08CS], and perfectness is closed
under isomorphism, so the isomorphism closure in the definition of saturation is the property
itself.  For a scheme `X`, whose `X.Modules` is `OXMod` of `X.toRingedSpace`, this is the
saturation clause of Tag 0F8I: a direct summand of a perfect object of `D(O_X)` is perfect. -/
@[stacks 0F8I "`D_perf(O_X)` is a saturated subcategory of `D(O_X)` -- the adjective `saturated` \
of the source's item (3), which is closure under direct summands, on any ringed space"]
theorem isSaturated_isPerfect {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] :
    ObjectProperty.IsSaturated
      (fun K : DerivedCategory (OXMod.{u, u} X) => IsPerfect K) :=
  isSaturated_isPerfect_of_biprod Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
