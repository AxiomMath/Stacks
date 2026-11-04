module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectTowerBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismSmallerBase

/-!
# Effectivity of formal objects for a separated `X'`, from Grothendieck existence

In the situation of Stacks 0GH8 with `X' ⟶ S` separated, the tower form of Stacks 0A4Z holds for
`X'` as soon as closed subspaces of the thickenings of proper algebraic spaces over Noetherian
complete affine bases algebraize (Stacks 08BG,
`AlgebraicGeometry.Space.ClosedSubspaceTowerAlgebraizes`), and then every formal object of
Artin's functor `F` is effective (Stacks 0GI8).

## Main results

* `ContractionSituation.hasEffectiveFormalObjects_of_closedSubspaceTowerAlgebraizes`: if `X' ⟶ S`
  is separated and towers of closed subspaces of algebraic spaces over Noetherian affine bases
  algebraize (`AlgebraicGeometry.Space.ClosedSubspaceTowerAlgebraizes`), every formal object of
  `F` is effective.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)

attribute [local instance] Space.isAffine_toScheme_baseObject

/-- If `X' ⟶ S` is separated and, over every Noetherian affine base `Spec R` with an ideal `J`,
towers of closed subspaces of the thickenings of algebraic spaces algebraize
(`AlgebraicGeometry.Space.ClosedSubspaceTowerAlgebraizes`), then every formal object of Artin's
functor `F` is effective. -/
theorem hasEffectiveFormalObjects_of_closedSubspaceTowerAlgebraizes
    (hclosed : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
      (J : Ideal Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj (Space.baseObject R B hR), ⊤))
      (W' : AlgebraicSpaces B (Spec (.of R)) hR) (f' : W' ⟶ schemeSpace (Space.baseObject R B hR)),
        Space.ClosedSubspaceTowerAlgebraizes (Space.baseObject R B hR) J f')
    (hX' : Space.IsSeparated B S hS (terminal.from c.X')) :
    LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c) :=
  c.hasEffectiveFormalObjects_of_hasProperTowerAlgebraizationOverSpec
    (Space.hasProperTowerAlgebraizationOverSpec_of_closedSubspaceTowerAlgebraizes hclosed
      c.isAlgebraicSpace_X' hX' c.isLocallyOfFiniteType_X')

end AlgebraicGeometry.Artin.ContractionSituation

end
