module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.SaturationFromRetractModels
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# The Grothendieck group `K₀(X)` of a scheme

`K₀(X)` is the zeroth `K`-group of `D_perf(𝒪_X)`, the strictly full, saturated, triangulated
subcategory of `D(𝒪_X)` whose objects are the perfect ones.

## Main definitions

* `AlgebraicGeometry.PerfectKZero` is `K₀(X)`.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isSaturated`: `D_perf(𝒪_X)`
  is saturated in `D(𝒪_X)`, that is, closed under direct summands.

## Implementation notes

The subcategory is `Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`, the full
subcategory of `DerivedCategory X.Modules` cut out by perfectness in the sense of Tag 08CM, read
on the ringed space underlying `X`. Each of the three adjectives the source attaches to it is
already available: strict fullness is
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isClosedUnderIsomorphisms`,
the triangulated structure is
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isTriangulated` (Tag 08CR),
and saturation is proved below from Tag 08CS.

Saturation appears twice in the trees already, in the modules `SaturationFromRetractModels`
and `SaturationFromPseudoCoherence` of
`StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes`,
in both cases with the content of Tag 08CS carried as a hypothesis because that tag was then
unproved. It is now `Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`, so the hypothesis is
discharged here and the conclusion is unconditional.

The `K`-group is `CategoryTheory.Pretriangulated.K0`, the free abelian group on the objects of a
pretriangulated category modulo the relations of its distinguished triangles, which is what the
source's Tag 0FCN defines; the class of a perfect object is
`CategoryTheory.Pretriangulated.K0.cls`. `PerfectKZero` is an abbreviation, so it inherits that
whole API rather than restating it, exactly as `AlgebraicGeometry.CoherentKZero` does for the
coherent group `K'₀(X)`.

The derived category is the standard one, as everywhere else in the Tag 0F8I development that
`PerfectDerivedCategory` comes from.

## References

* [Stacks Project, Tag 0FDG](https://stacks.math.columbia.edu/tag/0FDG)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 0FCN](https://stacks.math.columbia.edu/tag/0FCN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- **`D_perf(𝒪_X)` is a saturated subcategory of `D(𝒪_X)`**: both summands of a perfect
biproduct are perfect. This is Tag 08CS, read on the ringed space underlying `X` at the standard
derived-category universe, fed to
`Stacks.Perfect.BoundedLocallyFreeComplexes.isSaturated_isPerfect_of_biprod`. -/
@[stacks 0FDG "(1) D_perf(𝒪_X) is SATURATED in D(𝒪_X) — the third of the three adjectives \
Definition 0FDG (1) attaches to the subcategory whose K-group it names, and the only one the \
definition does not consume as an instance. The definitional clause itself is \
`AlgebraicGeometry.PerfectKZero`"]
theorem perfectDerivedProperty_isSaturated (X : Scheme.{u}) :
    (show ObjectProperty (DerivedCategory X.Modules) from
      fun K => IsPerfect (X := X.toRingedSpace) K).IsSaturated :=
  @isSaturated_isPerfect_of_biprod.{u, u, u + 1} X.toRingedSpace inferInstance
    (@Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod.{u} X.toRingedSpace inferInstance)

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

namespace AlgebraicGeometry

section

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 0FDG (1).** The *Grothendieck group* `K₀(X)` of a scheme `X`: the
zeroth `K`-group of the strictly full, saturated, triangulated subcategory `D_perf(𝒪_X)` of
`D(𝒪_X)` consisting of the perfect objects. -/
@[stacks 0FDG "(1) the DEFINITIONAL clause: K₀(X) := K₀(D_perf(𝒪_X)). Being a definition this \
states nothing on its own; the three adjectives the source attaches to D_perf(𝒪_X) are the \
assertional part of (1) and are registered separately, on \
`perfectDerivedProperty_isClosedUnderIsomorphisms` (strictly full), \
`perfectDerivedProperty_isTriangulated` (triangulated) and \
`perfectDerivedProperty_isSaturated` (saturated)"]
abbrev PerfectKZero (X : Scheme.{u}) : Type _ :=
  Pretriangulated.K0 (Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X)

end

end AlgebraicGeometry

end
