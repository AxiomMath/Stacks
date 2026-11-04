module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FibredMixedTensorProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The sets of sections of the structure sheaf of a fibred site

The universe lift of the coefficient rings of a ringed site is a sheaf of rings as soon as the
*sets* of sections of the original rings form a sheaf of sets.  That hypothesis is not implied
by the sheaf condition in `RingCat.{r}` when the site does not fit inside `Type r`: the latter
is a universal property tested against rings with sections in `Type r`, and reading it off on
underlying sets requires the limits over the covering sieves to be computed there.

This file supplies the hypothesis on an associated site of a category fibred in groupoids over
the big fppf category of schemes over a base, where the rings have sections in the universe `u`
of that base, the site has morphisms in `u` and objects in an unrelated universe.  As for
abelian groups, the route is essential smallness of the fibred category rather than a universe
inequality: on a site which is essentially small at `z`, a sheaf of rings with sections in
`max v z` has a sheaf of sets of sections, with `v` the universe of the morphisms of the site
and no condition on the universe of its objects.

## Main results

* `CategoryTheory.hasSheafCompose_forget_ringCat_of_essentiallySmall`: on a site which is
  essentially small at `z`, the presheaf of sections of a sheaf of rings with sections in
  `max v z` is a sheaf of sets.
* `AlgebraicGeometry.FibredSite.structureRingPresheaf_isSheafOfSets`: **the sets of sections of
  the structure sheaf of an associated site of an essentially small category fibred in
  groupoids form a sheaf**, which is the hypothesis under which the universe of its coefficient
  rings may be raised.

## Implementation notes

The sheaf condition is transported from the small model of the fibred category, exactly as
`CategoryTheory.hasSheafCompose_forget_addCommGrpCat_of_essentiallySmall` transports it for
abelian groups: a category essentially small at `z` is essentially small at `max v z`, and on a
site whose objects and morphisms both lie in one universe the library has the composition
instance for a concrete category with the right limits and filtered colimits.

The sheaf condition in `RingCat` is read off `AlgebraicGeometry.ringStructureSheafCore` rather
than through the named equation for it on the fibred site, which is stated only for a fibred
category whose objects lie in `Type (u + 1)`; here they lie in an arbitrary universe.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory

universe z u₁ v₁ u v

namespace CategoryTheory

/-- On a site which is essentially small at `z`, the presheaf of sections of a sheaf of rings
with sections in `max v z` is a sheaf of sets.  The universe of the sections need not contain
the universe of the objects of the site. -/
theorem hasSheafCompose_forget_ringCat_of_essentiallySmall {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{z} C] :
    J.HasSheafCompose (forget RingCat.{max v₁ z}) :=
  have : EssentiallySmall.{max v₁ z} C := essentiallySmall_lift C
  inferInstance

end CategoryTheory

namespace AlgebraicGeometry.FibredSite

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) [EssentiallySmall.{u} 𝒳]

/-- **The sets of sections of the structure sheaf of an associated site of an essentially small
category fibred in groupoids form a sheaf of sets.**  This is the hypothesis under which the
universe of the coefficient rings of the site may be raised, by
`Stacks.Modules.isSheaf_structureRingPresheaf_ringULift`; the sheaf condition in `RingCat.{u}`
does not imply it, the objects of the fibred category lying in an unrelated universe. -/
theorem structureRingPresheaf_isSheafOfSets (τ : SiteKind) :
    Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p τ)
      (structureRingPresheaf (structureSheaf B S hS p hp τ).obj ⋙
        forget RingCat.{u}) :=
  (hasSheafCompose_forget_ringCat_of_essentiallySmall.{u, v, u}
    (BigFppfOver.associatedTopology B S hS p τ)).isSheaf _
      (ringStructureSheafCore B S hS p hp τ).property

end AlgebraicGeometry.FibredSite

end
