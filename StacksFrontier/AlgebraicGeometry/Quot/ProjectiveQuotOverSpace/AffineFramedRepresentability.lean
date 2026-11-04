/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.FramedRepresentability
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.SerreLift
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.HilbertPolynomialComparison
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialSurjection

/-!
# `Quot^P` on `B × ℙⁿ_ℤ` over an affine `B` is represented by a proper scheme

Let `F/X/B` be a Quot situation with a projective frame `X = B × ℙⁿ_ℤ`, `B ≅ h_W` for an affine
scheme `W`, `F` of finite type, and `𝓛` the pullback of `𝒪(1)`.  This is the affine case of
the proof of Stacks 0DPB: by Stacks 01Q3, `F` is a quotient of a module `F₀` read on `ℙⁿ_W` as
`𝒪(-d)^{⊕ r}`; `Quot^P` of `F₀` is represented by a proper scheme
(`AlgebraicGeometry.ProjectiveQuotOverSpace.isRepresentedProper_hilbertSubfunctor_framed`, through
the comparison of Hilbert polynomials with respect to `𝓛`), and so is its closed subfunctor
`Quot^P` of `F` (Stacks 0DP5).

## Main results

* `isRepresentedProper_hilbertPolynomialQuot_twistingModule_of_affine`: `Quot^P` of `F` over an
  affine base is represented by a proper scheme.

## References

* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0DP5](https://stacks.math.columbia.edu/tag/0DP5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **Stacks 0DPB over an affine base, in terms of representability.** -/
theorem isRepresentedProper_hilbertPolynomialQuot_twistingModule_of_affine
    (D : Space.QuotSituation B integerBase B.contains_integerBase) (E : ProjectiveFrame B n D)
    {W : BigFppfOver B integerBase B.contains_integerBase} (φ : schemeSpace W ≅ D.Y)
    [IsAffine ((𝒯).obj W)] (hft : SheafOfModules.IsFiniteTypeOnSite D.F)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    D.IsRepresentedProper (D.hilbertPolynomialQuot (twistingModule E) P) := by
  obtain ⟨d, r, hr, F₀, hF₀, c, q, hq⟩ := exists_epi_baseSpaceIso_inv_pullback E φ hft
  let D'' : Space.QuotSituation B integerBase B.contains_integerBase :=
    { X := D.X
      Y := D.Y
      f := D.f
      F := framedModule E φ F₀
      quasicoherent := isQuasicoherentOnSite_framedModule E φ F₀ hF₀
      finitePresentation := D.finitePresentation }
  let E'' : ProjectiveFrame B n D'' := ⟨E.toProjective, E.isPullback⟩
  have h₁ := isRepresentedProper_hilbertSubfunctor_framed E'' φ F₀ hF₀ (Iso.refl _) hr c p
  rw [← hilbertPolynomialQuot_twistingModule_eq E'' hP] at h₁
  exact @Space.QuotSituation.isRepresentedProper_hilbertPolynomialQuot_withModule B integerBase
    B.contains_integerBase D'' D.F D.quasicoherent q hq (twistingModule E'') _ P h₁

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
