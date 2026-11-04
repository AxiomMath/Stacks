module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Cofiltered cones of affine objects of the big fppf site

The limit-preservation predicate of Stacks 07XL, `Deformation.Artin.IsLimitPreserving`, presents
an inverse system of affine schemes of the big fppf site as a diagram `D : I ⥤ BigAffineFppf`
together with a cone `c` whose cone of *underlying schemes* is a limit. The same system can also
be read in the big fppf category itself, or in the category of presheaves on it.

This file records that the three readings agree. A cone over a connected diagram in the big fppf
category whose cone of underlying schemes is a limit is already a limit in the big fppf category:
the underlying-scheme functor is the forgetful functor of a slice followed by a fully faithful
inclusion, and the first creates connected limits while the second reflects all of them. Yoneda
then carries that limit to a limit of presheaves, so an inverse system of affine schemes of the
site has the *same* limit whether it is taken in schemes, in the site, or in presheaves on the
site.

## Main results

* `AlgebraicGeometry.BigFppfOver.isLimit_of_isLimit_toScheme`: a connected cone of the big fppf
  category whose cone of underlying schemes is a limit is a limit.
* `AlgebraicGeometry.BigAffineFppf.isLimit_inclusion_mapCone`: the same for a cone of affine
  objects, read in the big fppf category.
* `AlgebraicGeometry.BigAffineFppf.isLimit_yoneda_mapCone`: the Yoneda image of such a cone is a
  limit of presheaves on the site.
* `CategoryTheory.Limits.isLimit_forget_pullback_overPost`: the base change of a cofiltered limit
  along a morphism out of a stage is a limit.

## Implementation notes

The index category of `AlgebraicGeometry.BigFppfOver.isLimit_of_isLimit_toScheme` is connected
rather than cofiltered, which is all that is used; a cofiltered index category is connected by
`CategoryTheory.IsCofiltered.isConnected`.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A connected cone of the big fppf category is a limit as soon as its cone of underlying
schemes is.** The underlying-scheme functor is the forgetful functor of the slice followed by the
fully faithful inclusion of the site's underlying category into schemes; the forgetful functor
creates connected limits and a fully faithful functor reflects all limits. -/
def BigFppfOver.isLimit_of_isLimit_toScheme {I : Type v} [Category.{w} I] [IsConnected I]
    {D : I ⥤ BigFppfOver B S hS} {c : Cone D}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) : IsLimit c :=
  isLimitOfReflects (BigFppfOver.toScheme B S hS) hc

/-- **A cofiltered cone of affine objects of the big fppf site, read in the big fppf category.**
The cone of objects of the big fppf category underlying a cone of affine objects whose cone of
schemes is a limit is itself a limit. -/
def BigAffineFppf.isLimit_inclusion_mapCone {I : Type v} [Category.{w} I] [IsCofiltered I]
    {D : I ⥤ BigAffineFppf B S hS} {c : Cone D}
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    IsLimit ((BigAffineFppf.inclusion B S hS).mapCone c) :=
  haveI : IsConnected I := IsCofiltered.isConnected I
  BigFppfOver.isLimit_of_isLimit_toScheme B S hS hc

/-- **The Yoneda image of a cofiltered cone of affine objects of the big fppf site is a limit of
presheaves.** Yoneda preserves limits, and the cone is a limit in the big fppf category by
`AlgebraicGeometry.BigAffineFppf.isLimit_inclusion_mapCone`. -/
def BigAffineFppf.isLimit_yoneda_mapCone {I : Type v} [Category.{w} I] [IsCofiltered I]
    {D : I ⥤ BigAffineFppf B S hS} {c : Cone D}
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    IsLimit ((yoneda (C := BigFppfOver B S hS)).mapCone
      ((BigAffineFppf.inclusion B S hS).mapCone c)) :=
  isLimitOfPreserves (yoneda (C := BigFppfOver B S hS))
    (BigAffineFppf.isLimit_inclusion_mapCone B S hS hc)

end AlgebraicGeometry

namespace CategoryTheory.Limits

universe v' w' u' uC vC

/-- **The base change of a cofiltered limit along a morphism out of a stage is a limit.** Let `c`
be a limiting cone over a cofiltered diagram `E`, let `i` be a stage and let `q : U ⟶ E i` be any
morphism. Restricting `c` to the stages over `i`, base changing it along `q` and forgetting the
structure morphism gives a limiting cone over the diagram `j ↦ U ×_{E i} E j`, with vertex
`U ×_{E i} c.pt`.

No smallness or cardinality hypothesis enters: the restriction to the stages over `i` is a limit
because `Over i ⥤ I` is initial for a cofiltered `I`
(`CategoryTheory.Over.initial_forget`, through `CategoryTheory.Limits.IsLimit.overPost`), base
change is a right adjoint and so preserves every limit, and the forgetful functor of a slice
preserves connected limits. -/
noncomputable def isLimit_forget_pullback_overPost {C : Type uC} [Category.{vC} C] [HasPullbacks C]
    {I : Type v'} [Category.{w'} I] [IsCofiltered I] {E : I ⥤ C} {c : Cone E} (hc : IsLimit c)
    (i : I) {U : C} (q : U ⟶ E.obj i) :
    IsLimit ((CategoryTheory.Over.forget U).mapCone
      ((CategoryTheory.Over.pullback q).mapCone (c.overPost i))) :=
  haveI : IsConnected (CategoryTheory.Over i) := IsCofiltered.isConnected _
  isLimitOfPreserves (CategoryTheory.Over.forget U)
    (isLimitOfPreserves (CategoryTheory.Over.pullback q) (hc.overPost i))

end CategoryTheory.Limits

end
