module

public import StacksFrontier.AlgebraicGeometry.FormalSectionsAlgebraization.HigherDegreeAdicLimit

/-!
# The input of Theorem 0EIE to Stacks 0EG4

Under hypotheses (1) and (2) of Stacks 0EG4, Lemma 0EFW produces a bootstrap situation
(Situation 0EFU) for `A, I, V(a), M, s, cd(A, I)`; the assertion of Theorem 0EIE for it gives
that the cones `H^i_{V(a)}(M) → lim H^i_{V(a)}(M/IⁿM)` are limit cones and the systems are
Mittag-Leffler in degrees `i ≤ s`. This file records that passage, as an implication from the
assertion of Theorem 0EIE.

## Main results

* `Stacks.Algebraization.localCohomologyAdicCone_zeroLocus_of_essentiallyConstant`.

## References

* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFW](https://stacks.math.columbia.edu/tag/0EFW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Algebraization

/-! ### The input from Theorem 0EIE -/

section Bootstrap


variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A) (hIa : I ≤ a)
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

include hIa in
/-- **What Theorem 0EIE gives on `V(a)`.** If, for every bootstrap situation, the systems
`{H^i_T(M/IⁿM)}` are essentially constant with value `H^i_T(M)` in degrees `i ≤ s`
(the assertion of Theorem 0EIE, `hEC`), then under hypotheses (1) and (2) of Stacks 0EG4 the cones
`H^i_{V(a)}(M) → lim H^i_{V(a)}(M/IⁿM)` are limit cones and the systems are Mittag-Leffler for
`i ≤ s`. The bootstrap situation is the one of Lemma 0EFW for `A, I, V(a), M, s, cd(A, I)`. -/
theorem localCohomologyAdicCone_zeroLocus_of_essentiallyConstant (s : ℤ)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{max u w} A), Dualizing.IsDualizingComplex K)
    (hdepth : SourceDepthHypothesis I a M s)
    (hEC : ∀ (S : BootstrapSituation.{u, u, w}) (i : ℤ), i ≤ S.s →
      ∃ (j : ℕᵒᵖ) (σ : (Bootstrap.tower.{u, u} S i).obj j ⟶ (Bootstrap.cone.{u, u} S i).pt),
        EssentiallyConstantPro.IsEssentiallyConstantWith
          (Bootstrap.tower.{u, u} S i) (Bootstrap.cone.{u, u} S i) j σ)
    (i : ℤ) (hi : i ≤ s) :
    Nonempty (IsLimit (localCohomologyAdicCone.{u, u} A
        (PrimeSpectrum.zeroLocus (a : Set A)) I i (ModuleCat.of A M))) ∧
      IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} A
        (PrimeSpectrum.zeroLocus (a : Set A)) I i (ModuleCat.of A M)) := by
  classical
  have hdepth' : ∀ p q : PrimeSpectrum A, p.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      q ∈ PrimeSpectrum.zeroLocus (a : Set A) →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) > (s : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
        ((Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing + s :
          ℤ) : EInt)) := by
    intro p q hpq hpI hqa
    rcases hdepth p hpI with h | h
    · exact Or.inl h
    · refine Or.inr (lt_of_le_of_lt ?_ (h q hpq hqa))
      have : (Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing + s)
          ≤ (Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing
            + s + 1) := by omega
      exact WithBotTop.coe_le_coe.mpr this
  obtain ⟨S, hA, hCR, hNo, hI, hM, hACG, hMod, hFin, hT, hs, -⟩ :=
    exists_bootstrapSituation_of_depth_gt_or_depth_add_dim_gt.{u, u, w} I a hIa (M := M) s
      (Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing) hdual le_rfl
      hdepth'
  obtain ⟨A₀, I₀, M₀, T₀, hsub, hstab, s₀, d₀, hdu, hcd, hdd, hcl⟩ := S
  dsimp only at hA hCR hNo hI hM hACG hMod hFin hT hs
  subst hA
  obtain rfl := eq_of_heq hCR
  obtain rfl := eq_of_heq hNo
  subst hM
  obtain rfl := eq_of_heq hACG
  obtain rfl := eq_of_heq hMod
  obtain rfl := eq_of_heq hFin
  obtain rfl := eq_of_heq hI
  subst hs
  have hT' : T₀ = PrimeSpectrum.zeroLocus (a : Set A₀) := eq_of_heq hT
  clear hT
  subst hT'
  obtain ⟨j, σ, hcon⟩ :=
    hEC
      { A := A₀, I := I₀, M := M₀, T := PrimeSpectrum.zeroLocus (a : Set A₀)
        subset_adicLocus := hsub, stableUnderSpecialization := hstab, s := s₀, d := d₀
        dualizing := hdu, cohomologicalDimension_le := hcd
        depth_or_depth_add_dimension := hdd, completedLocalDepth := hcl } i hi
  refine ⟨⟨Bootstrap.isLimit _ i hi hcon⟩, ?_⟩
  exact hcon.isMittagLefflerCategorical

end Bootstrap

end Stacks.Algebraization

end
