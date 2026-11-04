module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.FpqcLocal
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal injectivity is fpqc local on the base

A property `P` of morphisms of schemes is *fpqc local on the base* when, for every fpqc covering
`{Yᵢ → Y}` and every morphism `f : X ⟶ Y`, the morphism `f` has `P` if and only if each base
change `Yᵢ ×_Y X ⟶ Yᵢ` has `P`. This is Stacks Project Definition 35.22.1, and in Mathlib it is
`CategoryTheory.MorphismProperty.IsLocalAtTarget P AlgebraicGeometry.Scheme.fpqcPrecoverage`.

This file records that the property "`f` is universally injective" is fpqc local on the base.

## Main results

* `AlgebraicGeometry.universallyInjective_iff_of_fpqcCover` is the assertion in the shape in which
  the Stacks Project states locality on the base: for an fpqc covering `𝒰` of the target, a
  morphism is universally injective if and only if each of its base changes along a member of `𝒰`
  is.

## Implementation notes

The class-shaped form of the statement,
`AlgebraicGeometry.universallyInjective_isLocalAtTarget_fpqc`, already carries this tag where it
is proved, in `StacksFrontier/AlgebraicGeometry/Spaces/Representable/FpqcLocal.lean`. The iff below
is the unbundled reading of that instance, obtained from
`CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover`, and it is added because
`IsLocalAtTarget` is a class whose content is not visible in the shape the Stacks Project uses
to state Definition 35.22.1; it is universe-general in the index as well as in the schemes.

Stability of universal injectivity under base change and its Zariski locality on the base are the
first two of the three inputs the Stacks proof feeds to Tag 02KP; by themselves they do not give
fpqc locality, for which the third input — descent along a flat surjective morphism of affine
schemes — is needed. That input is
`AlgebraicGeometry.descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact`, and
the route taken in `StacksFrontier/AlgebraicGeometry/Spaces/Representable/FpqcLocal.lean` instead
descends injectivity on points directly along the joint surjectivity of an fpqc family, which is
the same argument with the field `K` of the Stacks proof replaced by a point of the fibre product.

## References

* [Stacks Project, Tag 02KW](https://stacks.math.columbia.edu/tag/02KW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe w u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02KW.** Universal injectivity is fpqc local on the base: for an fpqc
covering `𝒰` of `Y`, a morphism `f : X ⟶ Y` is universally injective if and only if each base
change `𝒰.X i ×_Y X ⟶ 𝒰.X i` is universally injective. -/
@[stacks 02KW]
theorem universallyInjective_iff_of_fpqcCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage Y) :
    UniversallyInjective f ↔ ∀ i, UniversallyInjective (pullback.snd f (𝒰.f i)) :=
  IsLocalAtTarget.iff_of_zeroHypercover
    (P := (@UniversallyInjective : MorphismProperty Scheme.{u})) 𝒰

end AlgebraicGeometry

end
