module

public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineHom

/-!
# The resolution property in a limit of schemes with affine transition morphisms

[Stacks, Tag 0F8B] states that for `X = lim X i` a limit of a cofiltered diagram of
quasi-compact, quasi-separated schemes with affine transition morphisms, `X` has the resolution
property if and only if some `X i` does.

This file proves the direction from a stage to the limit.  The projection `X ⟶ X i` out of such
a limit is affine (`AlgebraicGeometry.EventualLimit.isAffineHom_π_app`), so the affine case of
[Stacks, Tag 0F88] carries the resolution property from `X i` to `X`.  The converse and the
equivalence are in `StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyLimitStageQcqs.lean`
(`AlgebraicGeometry.hasResolutionProperty_iff_exists_of_isLimit`).

## Main results

* `AlgebraicGeometry.hasResolutionProperty_of_isLimit`: if a stage of the diagram has the
  resolution property, so does the limit.

## Implementation notes

The diagram convention is the one Mathlib's `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`
fixes and the `ModuleLimits` files of this repository follow: a functor `D : I ⥤ Scheme` out of a
cofiltered index category, a cone `c` with `IsLimit c`, affine transitions as the instance
hypothesis `∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)`, the limit as `c.pt` and the projections
as `c.π.app i`.  The hom universe of `I` is left free, so
`AlgebraicGeometry.EventualLimit.isAffineHom_π_app` is used rather than Mathlib's
`AlgebraicGeometry.isAffineHom_π_app`, which pins it to `u`.

## References

* [Stacks Project, Tag 0F8B](https://stacks.math.columbia.edu/tag/0F8B)
* [Stacks Project, Tag 0F88](https://stacks.math.columbia.edu/tag/0F88)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace AlgebraicGeometry

variable {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Let `c` be a limit cone over a cofiltered diagram `D` of quasi-compact, quasi-separated
schemes with affine transition morphisms.  If some stage `D.obj i` has the resolution property,
then so does the limit `c.pt`.

The projection `c.π.app i : c.pt ⟶ D.obj i` is affine, so this is the affine case of
[Stacks, Tag 0F88]; it is one direction of [Stacks, Tag 0F8B]
(`AlgebraicGeometry.hasResolutionProperty_iff_exists_of_isLimit`). -/
@[stacks 0F8B "the direction that is immediate: if a stage of the diagram has the resolution \
property then so does the limit"]
theorem hasResolutionProperty_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) [HasResolutionProperty (D.obj i)] :
    HasResolutionProperty c.pt :=
  have := EventualLimit.isAffineHom_π_app D c hc i
  hasResolutionProperty_of_isAffineHom (c.π.app i)

end AlgebraicGeometry

end
