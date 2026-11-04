module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image along the inclusion of a thickening is an equivalence

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S` and `i : G ⟶ X` its
inclusion.  The direct image of sheaves of sets along `i` is an equivalence of categories: it is
fully faithful because `i` is a closed immersion, by [Stacks Project, Tag 04E5] part (1), and
essentially surjective because `G ⊂ X` is a thickening.  Hence so is the inverse image, being
its left adjoint.

This is the sheaf-of-sets half of [Stacks Project, Tag 05ZM] read on the *inverse* image rather
than on the direct image.  It is the form in which the equivalence enters a cancellation: the
units square of [Stacks Project, Tag 04HA] is written in the inverse image, so to recognise a
square on the site of `X` from its image on the site of `G` one needs the inverse image to be
full and to reflect limits, which is what being an equivalence supplies.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_pushforward_inclusion_of_isThickening`: the direct
  image of sheaves of sets along the inclusion of a thickening is an equivalence.
* `AlgebraicGeometry.Space.isEquivalence_inverseImage_inclusion_of_isThickening`: hence so is
  the inverse image.

## Implementation notes

The two inputs are stated for the inclusion of a *closed subspace*
(`AlgebraicGeometry.Space.subspaceInclusion`) and for a closed immersion, and the inclusion of a
thickening is both: `AlgebraicGeometry.Space.IsThickening.inclusion` and
`AlgebraicGeometry.Space.subspaceInclusion` at the closed subspace `⟨G, hG.1⟩` are the same
morphism `ObjectProperty.homMk G.ι`, which
`AlgebraicGeometry.Space.inclusion_eq_subspaceInclusion_of_isThickening` records.

Passing from the direct image to the inverse image is
`CategoryTheory.Adjunction.isEquivalence_left_of_isEquivalence_right` at the adjunction carried
by the morphism of topoi, so no comparison of the inverse image with a restriction functor is
needed.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1).
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- The inclusion of a thickening is the inclusion of the closed subspace it is. -/
theorem inclusion_eq_subspaceInclusion_of_isThickening (hG : IsThickening B S hS X G) :
    IsThickening.inclusion B S hS hG = subspaceInclusion B S hS X ⟨G, hG.1⟩ :=
  rfl

/-- **The direct image of sheaves of sets along the inclusion of a thickening is an
equivalence.**  It is fully faithful because the inclusion is a closed immersion
([Stacks Project, Tag 04E5] part (1)) and essentially surjective because the subspace is a
thickening. -/
theorem isEquivalence_pushforward_inclusion_of_isThickening (hG : IsThickening B S hS X G) :
    (smallEtaleRingedToposHom B S hS
      (IsThickening.inclusion B S hS hG)).toToposHom.pushforward.IsEquivalence :=
  let hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (IsThickening.inclusion B S hS hG) (isClosedImmersion_inclusion_of_isThickening B S hS hG)
  ⟨hff.faithful, hff.full,
    essSurj_smallEtalePushforward_of_isThickening B S hS ⟨G, hG.1⟩ hG⟩

/-- **The inverse image of sheaves of sets along the inclusion of a thickening is an
equivalence**, being the left adjoint of an equivalence. -/
theorem isEquivalence_inverseImage_inclusion_of_isThickening (hG : IsThickening B S hS X G) :
    (smallEtaleRingedToposHom B S hS
      (IsThickening.inclusion B S hS hG)).toToposHom.inverseImage.IsEquivalence :=
  have := isEquivalence_pushforward_inclusion_of_isThickening B S hS hG
  Adjunction.isEquivalence_left_of_isEquivalence_right
    (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)).toToposHom.adj

end AlgebraicGeometry.Space

end
