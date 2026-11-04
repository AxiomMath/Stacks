module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspaceULift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleExtensionPushforward
import all StacksFrontier.AlgebraicGeometry.FormalSpace.Representable

/-!
# The étale extension of an affine chart across a thickening is affine

Let `i : F₀ ⟶ F` be a monomorphism of presheaves on the big fppf site of `S` which is a
representable thickening, with `F` an algebraic space, and let `u₀ : h_G ⟶ F₀` be étale,
representably by schemes, with `G` affine. The pushforward `CategoryTheory.monoPushforward i u₀`
is étale over `F` (`AlgebraicGeometry.Space.hasSchemePropertyULift_etale_monoPushforward_π`,
Stacks 05ZH at a thickening of arbitrary order). This file shows that it is an algebraic space
and that it is represented by an affine object of the site: it receives the representable
thickening `h_G ⟶ i_* h_G` (the base change of `i`), so the thickening case of Stacks 07VT applies
(`AlgebraicGeometry.Space.exists_isAffine_iso_uliftYoneda_of_isRepresentableThickeningULift`).

This is the step of the proof of Stacks 0AIU in which an affine étale chart of one stage of a
system of thickenings is transported to a later stage and stays affine.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_monoPushforward`: the pushforward is an
  algebraic space.
* `AlgebraicGeometry.Space.exists_isAffine_iso_uliftYoneda_monoPushforward`: the pushforward of
  an affine chart is represented by an affine object of the site.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The étale extension of an étale morphism across a thickening is an algebraic space.** For
a monomorphism `i : F₀ ⟶ F` which is a representable thickening into an algebraic space `F`, and
`u₀ : C₀ ⟶ F₀` étale representably by schemes, the pushforward of `u₀` along `i` is an algebraic
space: it is étale over `F` representably by schemes, so representable by algebraic spaces, and
Stacks 02YS applies. -/
theorem isAlgebraicSpaceULift_monoPushforward
    {F₀ F C₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (i : F₀ ⟶ F) [Mono i]
    (hi : IsRepresentableThickeningULift.{u + 1} B S hS i)
    (hF : IsAlgebraicSpaceULift.{u + 1} B S hS F) (u₀ : C₀ ⟶ F₀)
    (hu₀ : HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) :
    IsAlgebraicSpaceULift.{u + 1} B S hS (monoPushforward i u₀) := by
  have hπ := hasSchemePropertyULift_etale_monoPushforward_π B S hS i hi u₀ hu₀
  refine isAlgebraicSpaceULift_of_isRepresentableByAlgebraicSpacesULift B S hS
    (monoPushforward.π i u₀) (fun U ξ ↦ ?_) hF
  exact isAlgebraicSpaceULift_of_iso B S hS (hπ.rep.isPullback ξ).flip.isoPullback
    (isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS _)

/-- **The étale extension of an affine chart across a thickening is affine.** For a monomorphism
`i : F₀ ⟶ F` which is a representable thickening into an algebraic space `F`, and
`u₀ : h_G ⟶ F₀` étale representably by schemes with `G` affine, the pushforward of `u₀` along
`i` is represented by an affine object of the site.

The unit `h_G ⟶ i_* h_G` is the base change of `i` along the projection of the pushforward
(`CategoryTheory.isPullback_monoPushforward_unit`), hence a representable thickening, and its
target is an algebraic space (`AlgebraicGeometry.Space.isAlgebraicSpaceULift_monoPushforward`);
so this is the thickening case of Stacks 07VT. -/
theorem exists_isAffine_iso_uliftYoneda_monoPushforward
    {F₀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (i : F₀ ⟶ F) [Mono i]
    (hi : IsRepresentableThickeningULift.{u + 1} B S hS i)
    (hF : IsAlgebraicSpaceULift.{u + 1} B S hS F)
    (G : BigFppfOver B S hS) (hG : IsAffine ((BigFppfOver.toScheme B S hS).obj G))
    (u₀ : uliftYoneda.{u + 1}.obj G ⟶ F₀)
    (hu₀ : HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) :
    ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (monoPushforward i u₀ ≅ uliftYoneda.{u + 1}.obj T) := by
  have := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS))
  have hunit : IsRepresentableThickeningULift.{u + 1} B S hS (monoPushforward.unit i u₀) :=
    MorphismProperty.of_isPullback (isPullback_monoPushforward_unit i u₀).flip hi
  exact exists_isAffine_iso_uliftYoneda_of_isRepresentableThickeningULift B S hS
    (monoPushforward.unit i u₀) (isAlgebraicSpaceULift_monoPushforward B S hS i hi hF u₀ hu₀)
    hunit G hG (Iso.refl _)

end AlgebraicGeometry.Space

end
