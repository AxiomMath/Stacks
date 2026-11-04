module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerConeDepth
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerCechComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CechAnnihilationFaltings

/-!
# Cohomology of a proper scheme and of the formal completion along an ample zero scheme

Let `k` be a field, `P` a proper scheme over `k`, `𝓛` an ample invertible `𝒪_P`-module,
`s ∈ Γ(P, 𝓛)` with zero scheme `Q = Z(s)` and infinitesimal neighbourhoods `Qₙ`, and `𝓕` a
coherent `𝒪_P`-module with restrictions `𝓕ₙ = 𝓕|_{Qₙ}`. This file proves [Stacks, Tag 0EL1]: if
`depth(𝓕_p) + dim({p}‾) > σ` at every `p ∈ P ∖ Q`, then `Hⁱ(P, 𝓕) → lim Hⁱ(Qₙ, 𝓕ₙ)` is an
isomorphism for `0 ≤ i < σ`.

## The argument

Let `A = Γ_*(P, 𝓛)` be the section ring, `M = Γ_*(P, 𝓛, 𝓕)` and `f ∈ A₁` the element named by `s`.

* `A` is a finite type `k`-algebra and `M` a finite `A`-module (Stacks 0B5T), and `P = Proj A`
  (Stacks 0EKI), so finitely many homogeneous generators `g₁, …, g_r` of positive degree of the
  irrelevant ideal give an affine open covering `P = ⋃ D₊(gᵢ)`
  (`Stacks.SectionPowerConeDepth.exists_charts`, `isAffineOpen_nvOpen`).
* The bound on `P ∖ Q` gives `depth(M_𝔭) + dim((A/𝔭)_𝔮) > σ + 1` for all primes `𝔭 ∌ f` and
  `𝔮 ⊇ 𝔭 + A₊` (`Stacks.SectionPowerConeDepth.depthAddRelativeDim_gt`), and Faltings' annihilator
  theorem (Stacks 0EFC) makes a power of `f` annihilate the cohomology of the Čech complex
  `C^•(g; M)` in degrees `≤ σ + 1` (`Stacks.Algebraization.exists_pow_smul_cechHomology_eq_zero`).
* The Čech complexes of the covering compute both `Hⁱ(P, 𝓕)` and `Hⁱ(Qₙ, 𝓕ₙ)` as the degree-zero
  parts of `C^•(g; M)` and of its quotients by `fⁿ`, and the annihilation makes the comparison an
  isomorphism in degrees `< σ`
  (`Stacks.SectionPowerCechComparison.isIso_zeroSchemeComparison_of_cech`).

## Main results

* `Stacks.Algebraization.isIso_zeroSchemeComparison_of_isProper`: [Stacks, Tag 0EL1].

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.GradedSections (powSections sectionRing)
open Stacks.TwistedSections (twistModule)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionPowerConeDepth

universe u

namespace Stacks.Algebraization

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **Stacks Tag 0EL1.** Let `k` be a field, `P` a proper scheme over `k`, `𝓛` an ample invertible
`𝒪_P`-module, `s ∈ Γ(P, 𝓛)` with zero scheme `Q` and `𝓕` a coherent `𝒪_P`-module. If
`depth(𝓕_p) + dim({p}‾) > σ` at every `p ∈ P ∖ Q`, then the comparison map
`Hⁱ(P, 𝓕) → lim Hⁱ(Qₙ, 𝓕ₙ)` is an isomorphism for `0 ≤ i < σ`. -/
@[stacks 0EL1 "The tower Qₙ is indexed from n = 0 and Qₙ is cut out by the n-th power of the ideal \
sheaf of Q = Z(s), which is the ideal sheaf of Z(sⁿ); the zeroth term is empty and does not change \
the limit. Depth and dimension are compared in the extended integers."]
theorem isIso_zeroSchemeComparison_of_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [IsProper π] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤)) (F : X.Modules) [F.IsCoherent] (σ : ℤ)
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      enatToEInt (sheafDepthAt F x) + krullDimToEInt (dimClosureAt X x) > (σ : EInt))
    (i : ℕ) (hi : (i : ℤ) < σ) :
    haveI : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
    IsIso (zeroSchemeComparison X L s F i) := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, σ = n := ⟨σ.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hin : i < n := by exact_mod_cast hi
  let := sectionRingAlgebra L k π
  have hft : Algebra.FiniteType k (sectionRing L) := RingHom.finiteType_algebraMap.mp
    (Stacks.AlgebraicGeometry.ProperAmpleCohomology.ringHomFiniteType_sectionRing π L hL)
  have : IsNoetherianRing (sectionRing L) := Algebra.FiniteType.isNoetherianRing k _
  have : Module.Finite (sectionRing L) (twistModule F L) :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.moduleFinite_twistModule_of_isCoherent π F L hL
  have : IsNoetherian (sectionRing L) (twistModule F L) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨r, d, α, hd, hspan, hcov⟩ := exists_charts L hL
  have haff : ∀ (e : ℕ) (β : powSections L e), 0 < e → IsAffineOpen (nvOpen L β) :=
    fun e β he => isAffineOpen_nvOpen L hL k π β he
  have hU : IsAffineOpen (nvOpen L (degreeOneSection L s)) := haff 1 _ one_pos
  have hf : Stacks.SectionRingChartTower.sectionElt L s ∈
      (Ideal.span (Set.range (Stacks.SectionRingChartCech.gen L α))).radical := by
    rw [hspan]
    exact Ideal.le_radical (Stacks.ExternalGrading.of_mem_irrelevant one_ne_zero _)
  obtain ⟨c, hH⟩ := exists_pow_smul_cechHomology_eq_zero k (sectionRing L)
    (twistModule F L) (Stacks.SectionRingChartCech.gen L α)
    (Stacks.SectionRingChartTower.sectionElt L s) hf n fun p q hp hq hpq => by
      refine depthAddRelativeDim_gt L hL s hU p hp k π F n hdepth q ?_ hpq
      rw [← hspan, Ideal.span_le]
      exact (PrimeSpectrum.mem_zeroLocus _ _).1 hq
  exact Stacks.SectionPowerCechComparison.isIso_zeroSchemeComparison_of_cech L hL F hd α hcov haff
    s hH i hin

end Stacks.Algebraization

end
