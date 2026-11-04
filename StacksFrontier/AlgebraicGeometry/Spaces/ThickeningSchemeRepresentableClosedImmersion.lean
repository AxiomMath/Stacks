module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentable

/-!
# The ambient space of a thickening of a scheme is a scheme, with nothing granted

Let `S` be a scheme and let `X ⊂ X'` be a thickening of algebraic spaces over `S`. If `X` is
(representable by) a scheme, then so is `X'`. This is Stacks 05ZR, and
`StacksFrontier/AlgebraicGeometry/Spaces/ThickeningSchemeRepresentable.lean` proves it granted the
three hypotheses of Stacks 07VT. This file proves the same two forms with no hypotheses beyond
the source's, and records Stacks 07VU.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable` and
  `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable`: Stacks 05ZR
  in the subspace form and in the morphism form, with no hypotheses, through the
  closed-immersion form of Stacks 07VV.
* The registration of Stacks 07VU, an algebraic space whose reduction is a scheme is a scheme,
  on `AlgebraicGeometry.IsAlgebraicSpace.isRepresentable_of_isRepresentable_reduction`.

## Implementation notes

`AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`, in
`StacksFrontier/AlgebraicGeometry/Spaces/SchemeOfSchemeReduction.lean`, takes the affineness step
from the thickening case of Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`, which is proved
with no hypotheses.

*Why Stacks 07VT does not enter.* Stacks 07VV is stated for an integral morphism, and for one
the affineness step of its proof is Stacks 07VT, whose library form
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed` grants the three
hypotheses `h09YA`, `h07SQ` and `hFinitePresentation`. The inclusion of a thickening is more
than integral: it is a *closed immersion*, so the projection of its base change along the open
subspace cut out in that proof is a closed immersion again, hence finite by Stacks 081Y, and
the affineness step is the affineness of the target of a surjective closed immersion with
affine source, the thickening case of Stacks 07VT, which holds with no hypotheses; that
narrowing is `AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`.

The inclusion `G.ι` of a thickening is injective on points because it is a monomorphism and
surjective on points by definition, which together give the bijectivity that Stacks 07VV
asks for; that it is a closed immersion is the first half of
`AlgebraicGeometry.Space.IsClosedSubspace`. In the morphism form the same three facts come
from `AlgebraicGeometry.Space.IsThickeningHom.mono`,
`AlgebraicGeometry.Space.IsThickeningHom.surjective_pointsMap` and
`AlgebraicGeometry.Space.IsThickeningHom.isClosedImmersion`.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05ZR, closed-immersion form.** Let `S` be a scheme and let `G ⊂ X'` be a
thickening of algebraic spaces over `S`, in the subspace form of Stacks 05ZK, part (1). If `G`
is (representable by) a scheme, then so is `X'`. This is
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_thickening` without the three
hypotheses of Stacks 07VT, the closed-immersion form of Stacks 07VV being unconditional.

The inclusion `G.ι` is a closed immersion, injective on points because it is a monomorphism,
and surjective on points by the definition of a thickening, so Stacks 07VV applies in the
direction that goes from the source, in its closed-immersion form. -/
theorem isRepresentable_of_isThickening_of_isRepresentable {X' : AlgebraicSpaces B S hS}
    {G : Subfunctor X'.1} (hG : IsThickening B S hS X' G)
    (hGrep : G.toFunctor.IsRepresentable) :
    X'.1.IsRepresentable :=
  isRepresentable_of_isClosedImmersion_of_bijective B S hS hG.1.1 X'.property G.ι
    hG.1.2 ⟨pointsMap_injective_of_mono B S hS G.ι, hG.2⟩ hGrep

/-- **Stacks 05ZR, morphism and closed-immersion form.** Let `S` be a scheme and let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S`, in the morphism form of
`AlgebraicGeometry.Space.IsThickeningHom`. If `X` is (representable by) a scheme, then so is
`X'`. This is `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom` without the three
hypotheses of Stacks 07VT, the closed-immersion form of Stacks 07VV being unconditional.

A thickening is a closed immersion, it is a monomorphism and therefore injective on points,
and it is surjective on points, so Stacks 07VV applies in the direction that goes from the
source, in its closed-immersion form. -/
theorem isRepresentable_of_isThickeningHom_of_isRepresentable {X X' : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (hi : IsThickeningHom B S hS i) (hXrep : X.1.IsRepresentable) :
    X'.1.IsRepresentable := by
  have := hi.mono
  exact isRepresentable_of_isClosedImmersion_of_bijective B S hS X.property X'.property i.hom
    hi.isClosedImmersion
    ⟨pointsMap_injective_of_mono B S hS i.hom, hi.surjective_pointsMap⟩ hXrep

end AlgebraicGeometry.Space

/-! ### Stacks 07VU

Stacks 07VU: let `X` be an algebraic space over `S`; if `X_red` is a scheme, then `X` is a
scheme. That is exactly the statement of
`AlgebraicGeometry.IsAlgebraicSpace.isRepresentable_of_isRepresentable_reduction` in
`StacksFrontier/AlgebraicGeometry/Spaces/SchemeOfSchemeReduction.lean`, with nothing granted:
`AlgebraicGeometry.Space.reduction` is the reduction `X_red` of Stacks 047X, and being a scheme
is `CategoryTheory.Functor.IsRepresentable`. -/

add_to_stacks 07VU AlgebraicGeometry.IsAlgebraicSpace.isRepresentable_of_isRepresentable_reduction

end
