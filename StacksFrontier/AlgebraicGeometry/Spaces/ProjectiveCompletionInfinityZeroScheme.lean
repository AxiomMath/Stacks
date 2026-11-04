module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSplitEpiZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionAffinePart

/-!
# The hyperplane at infinity of the projective completion is the zero scheme of `s`

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module of rank `r` and
`P = 𝐏(ℰ ⊕ 𝒪_X)` the projective completion of its vector bundle, with the global section
`s ∈ Γ(P, 𝒪_P(1))` of `(0, 1)` (`AlgebraicGeometry.Space.projectiveCompletionSection`). The
projection `ℰ ⊕ 𝒪_X ⟶ ℰ`, split by the inclusion of `ℰ`, gives the closed immersion
`i : 𝐏(ℰ) ⟶ P` of the hyperplane at infinity
(`AlgebraicGeometry.Space.projectiveCompletionInfinityImmersion`). This file proves that **its
image is the zero scheme `D = Z(s)`**, the effective Cartier divisor of Stacks 0847 with
`𝒪_P(D) ≅ 𝒪_P(1)` given by
`AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_zeroScheme_projectiveCompletionSection`.

## Main results

* `AlgebraicGeometry.Space.range_projectiveCompletionInfinityImmersion_eq_zeroScheme`: the image
  of `i` is the zero scheme `Z(s)`.
* `AlgebraicGeometry.Space.isClosedImmersion_projectiveCompletionInfinityImmersion`: `i` is a
  closed immersion.
* `AlgebraicGeometry.Space.projectiveCompletionSection_eq`: `s` is the hyperplane section of
  `𝒪_X ⟶ ℰ ⊕ 𝒪_X` of `AlgebraicGeometry.Space.projectiveBundleSection`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)

/-- **The hyperplane at infinity is a closed immersion.** -/
theorem isClosedImmersion_projectiveCompletionInfinityImmersion :
    IsClosedImmersion B S hS (projectiveCompletionInfinityImmersion E hr).hom :=
  @isClosedImmersion_projectiveBundleMapOfSplitEpi B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite

/-- The section `s` of `(0, 1)` is the hyperplane section of the inclusion `𝒪_X ⟶ ℰ ⊕ 𝒪_X`. -/
theorem projectiveCompletionSectionHom_eq :
    projectiveCompletionSectionHom E hr =
      @projectiveBundleSectionHom B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr) (addUnitInr X.2 E) := by
  unfold projectiveCompletionSectionHom projectiveBundleSectionHom
  with_reducible rfl

/-- The section `s ∈ Γ(P, 𝒪_P(1))` of `(0, 1)` is the hyperplane section of the inclusion
`𝒪_X ⟶ ℰ ⊕ 𝒪_X`. -/
theorem projectiveCompletionSection_eq :
    projectiveCompletionSection E hr =
      @projectiveBundleSection B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr) (addUnitInr X.2 E) := by
  unfold projectiveCompletionSection projectiveBundleSection
  rw [projectiveCompletionSectionHom_eq]

/-- **The image of the hyperplane at infinity `𝐏(ℰ) ⟶ P = 𝐏(ℰ ⊕ 𝒪_X)` is the zero scheme `Z(s)`
of the section `s` of `(0, 1)`**, as subfunctors of `P`. -/
theorem range_projectiveCompletionInfinityImmersion_eq_zeroScheme :
    Subfunctor.range (projectiveCompletionInfinityImmersion E hr).hom =
      (zeroScheme B S hS (projectiveCompletion E hr) (projectiveCompletionTwist E hr).obj
        (projectiveCompletionSection E hr)).1 := by
  have hsplit :
      addUnitSnd X.2 E ≫ addUnitInr X.2 E + biprod.fst ≫ biprod.inl = 𝟙 (addUnit X.2 E) := by
    rw [add_comm]
    exact biprod.total
  rw [projectiveCompletionSection_eq]
  exact @range_projectiveBundleMapOfSplitEpi_eq_zeroScheme B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite (addUnitInr X.2 E) (addUnitSnd X.2 E) hsplit biprod.inr_fst

end AlgebraicGeometry.Space

end
