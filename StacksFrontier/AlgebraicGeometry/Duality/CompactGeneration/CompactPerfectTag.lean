module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect

/-!
# Compact objects of `D_QCoh(𝒪_X)` are the perfect ones

For a quasi-compact quasi-separated scheme `X`, the compact objects of `D_QCoh(𝒪_X)` are exactly
the perfect objects of `D(𝒪_X)` lying in it: [Stacks, Tag 09M1], read as an equality of object
properties of `D_QCoh(𝒪_X)`, in every model of `D(𝒪_X)`.

## Main results

* `Stacks.Duality.isCompactObject_eq_isPerfect` — [Stacks, Tag 09M1].

## Implementation notes

The objectwise statement and its proof are `Stacks.Duality.isCompactObject_iff_isPerfect` in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/CompactPerfect.lean`, with its two
directions `Stacks.Duality.isPerfect_of_isCompactObject` and
`Stacks.Duality.isCompactObject_of_isPerfect`; nothing is assumed beyond the source's hypotheses
and a model of `D(𝒪_X)`.

## References

* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

/-- **[Stacks, Tag 09M1].** Let `X` be a quasi-compact and quasi-separated scheme. An object of
`D_QCoh(𝒪_X)` is compact if and only if it is perfect: the compact objects of `D_QCoh(𝒪_X)` are
exactly those whose underlying object of `D(𝒪_X)` is perfect, in any model of `D(𝒪_X)`. -/
@[stacks 09M1]
theorem isCompactObject_eq_isPerfect (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [h : HasDerivedCategory.{w} X.Modules] :
    (IsCompactObject.{u} : ObjectProperty (quasiCoherentDerivedCategory X)) =
      fun K => @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K.obj :=
  funext fun K => propext (isCompactObject_iff_isPerfect K)

end Stacks.Duality
