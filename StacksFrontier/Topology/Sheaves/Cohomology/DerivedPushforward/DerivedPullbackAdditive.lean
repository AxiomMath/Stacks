module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The derived pullback of a morphism of ringed spaces is additive

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  This file records the single
declaration

`(Lh^* : D(𝒪_Y) ⥤ D(𝒪_X)).Additive`.

## Why it is a file of its own

The additivity is not new: Mathlib derives it from exactness and the exactness of `Lh^*` is
Tag 06YJ, the global instance
`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated`.  What makes it worth a
file is that **instance search does not find it in the reducibility regime its consumers work
in**.  A consumer that mixes the pullback development's spelling of `𝒪_Y`
(`structureSheafRing`) with the tensor development's (`Stacks.SheafOfModules.Tensor.ringSheaf`)
— which every statement about the canonical map of Tag 08I3 does — must raise
`structureSheafRing` to `implicit` transparency, and that changes the discrimination-tree keys
the exactness and shift-commutation instances are filed under, so they are no longer found;
offering them as *local* instances restores those two goals but Mathlib's
`[F.IsTriangulated] → F.Additive`, the only route to additivity, still does not fire.  This holds in
every combination, including with `structureSheafRing` unraised and with
`AlgebraicGeometry.SheafedSpace.sheaf` raised alone.

So the additivity is proved here, in the instance regime of
`…DerivedPullback.Triangulated` itself — the same seating
`…DerivedPullback.PullbackTensorCommShiftTwo` performs for the same reason — and a consumer
offers the resulting theorem as a local instance instead of re-synthesizing it.  Its first consumer
is `…DerivedPushforward.InternalHomPullbackFiniteFree`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive`.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Cohomology.KFlatDerivedPullback.hasMapBifunctorSheafTensor

/-- **The derived pullback along a morphism of ringed spaces is additive.**  Mathlib derives
additivity from exactness, and the exactness of `Lh^*` is Tag 06YJ,
`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated`.

Proved here rather than synthesized at the point of use: see the implementation notes of this
file for the reducibility regime in which it stops being findable, which is the regime every
statement about the canonical map of Tag 08I3 lives in. -/
theorem derivedPullbackAdditive {X Y : RingedSpace.{u, u}} (h : X ⟶ Y) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).Additive :=
  inferInstance

end Stacks.Cohomology.DerivedInternalHomPullback

end
