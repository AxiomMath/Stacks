module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectSeparated
public import
  StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.InductionClosedSubspaceTower
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionBijectiveOnHomsBaseObject

/-!
# Effectivity of formal objects for a separated `X'`, from Grothendieck's existence theorem

In the situation of Stacks 0GH8 with `X' ⟶ S` separated, every formal object of Artin's functor
`F` is effective (Stacks 0GI8) as soon as, over Noetherian affine bases `Spec R` of the site, the
completion functor of a separated finite type algebraic space is fully faithful on modules with
proper support (Stacks 08B9, `AlgebraicGeometry.Space.CompletionBijectiveOnHoms`) and an
equivalence on modules with support proper over `R` (Stacks 08BE,
`AlgebraicGeometry.Space.CompletionProperOverIsEquivalence`). The chain is: these give the
algebraization of closed subspaces of the thickenings (Stacks 08BG), hence the tower form of
Stacks 0A4Z for `X'`, hence its completion form, hence effectivity.

## Main results

* `ContractionSituation.hasEffectiveFormalObjects_of_completionExistence`.
* `ContractionSituation.hasEffectiveFormalObjects_of_completionProperOverIsEquivalence`:
  the same with full faithfulness (Stacks 08B9) discharged.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)

attribute [local instance] Space.isAffine_toScheme_baseObject
  Space.isLocallyNoetherian_toScheme_baseObject

/-- **Stacks 0GI8, reduced to Grothendieck's existence theorem over Noetherian affine bases.** -/
theorem hasEffectiveFormalObjects_of_completionExistence
    (hhom : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
      (J : Ideal Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj (Space.baseObject R B hR), ⊤))
      (W' : AlgebraicSpaces B (Spec (.of R)) hR) (f' : W' ⟶ schemeSpace (Space.baseObject R B hR)),
        Space.CompletionBijectiveOnHoms (Space.baseObject R B hR) J f')
    (hequiv : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
      (J : Ideal Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj (Space.baseObject R B hR), ⊤))
      (W' : AlgebraicSpaces B (Spec (.of R)) hR) (f' : W' ⟶ schemeSpace (Space.baseObject R B hR)),
        Space.CompletionProperOverIsEquivalence (Space.baseObject R B hR) J f')
    (hX' : Space.IsSeparated B S hS (terminal.from c.X')) :
    LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c) :=
  c.hasEffectiveFormalObjects_of_closedSubspaceTowerAlgebraizes
    (fun R _ _ hR J W' f' => Space.closedSubspaceTowerAlgebraizes_of_existence _ J f'
      (hhom R hR J W' f') (hequiv R hR J W' f')) hX'

/-- **Stacks 0GI8, reduced to Grothendieck's existence theorem (Stacks 08BE)** over Noetherian
affine bases; the full faithfulness of completion (Stacks 08B9) is
`AlgebraicGeometry.Space.C1573.completionBijectiveOnHoms_baseObject`. -/
theorem hasEffectiveFormalObjects_of_completionProperOverIsEquivalence
    (hequiv : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
      (J : Ideal Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj (Space.baseObject R B hR), ⊤))
      (W' : AlgebraicSpaces B (Spec (.of R)) hR) (f' : W' ⟶ schemeSpace (Space.baseObject R B hR)),
        Space.CompletionProperOverIsEquivalence (Space.baseObject R B hR) J f')
    (hX' : Space.IsSeparated B S hS (terminal.from c.X')) :
    LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c) :=
  c.hasEffectiveFormalObjects_of_completionExistence
    (fun R _ _ hR J _ f' => Space.C1573.completionBijectiveOnHoms_baseObject R hR J f') hequiv hX'

end AlgebraicGeometry.Artin.ContractionSituation

end
