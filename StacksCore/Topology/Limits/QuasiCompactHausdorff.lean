module

import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# A limit of quasi-compact Hausdorff spaces is quasi-compact

This file proves Stacks 08ZV: if every space of a diagram `F : J ⥤ TopCat` is quasi-compact
(`CompactSpace`) and Hausdorff (`T2Space`), then every limit of `F` is quasi-compact. The index
category `J : Type v` with `Category.{w} J` is arbitrary: its universes are independent of the
universe `u` of the spaces, and `J` need not be small.

The proof lifts `F` to a diagram `F'` of compact Hausdorff spaces such that `F' ⋙ compHausToTop`
is `F` by definition. The inclusion `compHausToTop : CompHaus ⥤ TopCat` is reflective (its left
adjoint is the Stone–Čech compactification), hence monadic, so `monadicCreatesLimits` makes it
create limits of every size. A limit cone over `F` therefore lifts to a limit cone over `F'`.
The point of the lifted cone is compact and homeomorphic to the original cone point.

The argument in the Stacks project, which realizes the limit as a closed subspace of the product
`∏ F.obj j`, is the one Mathlib uses to construct the explicit limit cone `CompHaus.limitCone`.
That construction needs a small index category, so the proof here goes through creation of
limits instead.

## Main results

* `TopCat.compactSpace_of_isLimit` (Stacks 08ZV): the point of every limit cone over `F` is
  quasi-compact.
* `TopCat.compactSpace_limit`: the instance saying the same for the chosen limit `limit F`.

## Implementation notes

Mathlib's instance `compHausToTop.createsLimits` only provides `CreatesLimits compHausToTop`, that
is, creation of limits indexed by `J : Type u` with `Category.{u} J`. The proof of
`TopCat.compactSpace_of_isLimit` therefore installs `monadicCreatesLimits` at the universes of `J`
as a local instance. That local instance becomes unnecessary once Mathlib states
`compHausToTop.createsLimits` as `CreatesLimitsOfSize.{w, v} compHausToTop.{u}`.

## References

* [Stacks Project, Tag 08ZV](https://stacks.math.columbia.edu/tag/08ZV)
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace TopCat

/-- **Stacks 08ZV.** Let `F : J ⥤ TopCat` be a diagram such that every `F.obj j` is quasi-compact
(`CompactSpace`) and Hausdorff (`T2Space`). Then the point of any limit cone over `F` is
quasi-compact.

The index category `J : Type v` with `Category.{w} J` is arbitrary and need not be small.
The instance `TopCat.compactSpace_limit` is the case of the chosen limit `limit F`. In the Stacks
project the index category of a limit has a set of objects (Stacks 002G), which is the case
`J : Type u` with `SmallCategory J`. -/
@[stacks 08ZV]
theorem compactSpace_of_isLimit
    {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{u})
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
    (c : Cone F) (hc : IsLimit c) : CompactSpace c.pt :=
  let := monadicCreatesLimits.{w, v} compHausToTop.{u}
  let F' : J ⥤ CompHaus.{u} :=
    { obj j := { toTop := F.obj j, prop := ⟨⟩ }
      map f := InducedCategory.homMk (F.map f) }
  -- `F' ⋙ compHausToTop` is `F` by definition (this unfolds `compHausLikeToTop` and `homMk`).
  have w : F' ⋙ compHausToTop ≅ F := Iso.refl _
  let hc' := (IsLimit.postcomposeInvEquiv w c).symm hc
  let e : compHausToTop.obj (liftLimit hc').pt ≅ ((Cone.postcompose w.inv).obj c).pt :=
    (hc'.ofIsoLimit (liftedLimitMapsToOriginal hc').symm).conePointUniqueUpToIso hc'
  (TopCat.homeoOfIso e).compactSpace

/-- If every `F.obj j` is quasi-compact and Hausdorff, then the chosen limit `limit F` is
quasi-compact. This is `TopCat.compactSpace_of_isLimit` for the limit cone `limit.cone F`.
The instance `HasLimit F` is found by instance search whenever `Small.{u} J` is, for instance
when `J : Type u` and `SmallCategory J`. For any other limit cone, for example
`TopCat.limitCone F`, use `TopCat.compactSpace_of_isLimit`. -/
instance compactSpace_limit
    {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{u})
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
    [HasLimit F] : CompactSpace ↑(limit F) :=
  compactSpace_of_isLimit F _ (limit.isLimit F)

end TopCat
