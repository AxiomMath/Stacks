module

public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites
public import StacksFrontier.SetTheory.Cardinal.StrongPrelimitCofinality

/-!
# Big fppf sites of large cofinality

Every big fppf site is dominated by one whose cutoff has cofinality above any prescribed cardinal.
The construction is that of `AlgebraicGeometry.exists_common_bigFppfSite` for a single site, with
the cutoff taken from `Cardinal.exists_isStrongPrelimit_gt_of_lt_cof`.

## Main results

* `AlgebraicGeometry.exists_bigFppfSite_le_of_lt_cof`: an enlargement of one big fppf site whose
  cutoff has cofinality above a prescribed cardinal.
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A big fppf site is dominated by one of arbitrarily large cofinality.** For a big fppf site
`B` and a cardinal `lam` there is a big fppf site whose cutoff and covering bound dominate those
of `B` and whose cutoff has cofinality above `lam`.

The construction is that of `AlgebraicGeometry.exists_common_bigFppfSite` for the one site `B`,
with the cutoff supplied by `Cardinal.exists_isStrongPrelimit_gt_of_lt_cof` instead of
`Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof`. The cofinality bound is what the
descent results for inverse systems indexed by a set of size `lam` need of the site in which
they are applied. -/
theorem exists_bigFppfSite_le_of_lt_cof (B : AlgebraicGeometry.BigFppfSite.{u})
    (lam : Cardinal.{u}) :
    ∃ C : AlgebraicGeometry.BigFppfSite.{u},
      B.cutoff ≤ C.cutoff ∧ B.coveringBound ≤ C.coveringBound ∧ lam < C.cutoff.ord.cof := by
  classical
  obtain ⟨κ, hBκ, hstrong, hcof, hlam⟩ :=
    Cardinal.exists_isStrongPrelimit_gt_of_lt_cof B.cutoff lam
  let IsCov := AlgebraicGeometry.IsFppfCovering (κ := κ)
  have hsite : IsSite IsCov := isSite_fppfCutoff κ
  let Cov₀ : Set.{u + 2} (Covering.{u + 1, u, u + 1}
      (AlgebraicGeometry.SchemeBelow κ)) := ∅
  have : Small.{u + 1} Cov₀ := inferInstance
  obtain ⟨κ₀, α, hα, _, _, hrep⟩ :=
    exists_covBounded_isSite IsCov hsite Cov₀ (fun _ hU => by cases hU)
  let κcov := max ℵ₀ (max κ₀ B.coveringBound)
  have hrep' : ∀ U : Covering (AlgebraicGeometry.SchemeBelow κ), IsCov U →
      ∃ U', CovBounded IsCov κcov U' ∧ Covering.CombEquiv U U' := by
    intro U hU
    obtain ⟨U', hU', hcomb⟩ := hrep U hU
    exact ⟨U', ⟨hU'.1, hU'.2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩, hcomb⟩
  -- Imposing the infinite bound `κcov` on the index types keeps the site axioms (this is the
  -- private `covBounded_isSite_of_isSite` of `CommonBigSites`, for the one bound used here).
  have hκ : Cardinal.aleph0.{u + 1} ≤ κcov := le_max_left _ _
  have hsig : ∀ {I : Type (u + 1)}, #I ≤ κcov → ∀ {J : I → Type (u + 1)},
      (∀ i, #(J i) ≤ κcov) → #(Σ i, J i) ≤ κcov := by
    intro I hI J hJ
    calc
      #(Σ i, J i) = sum fun i => #(J i) := mk_sigma J
      _ ≤ #I * κcov := (sum_le_sum _ _ hJ).trans (by simp [sum_const])
      _ ≤ κcov * κcov := mul_le_mul' hI le_rfl
      _ = κcov := mul_eq_self hκ
  have hbsite : IsSite (CovBounded IsCov κcov) := by
    obtain ⟨hIso, hComp, hBC⟩ := hsite
    refine ⟨?_, ?_, ?_⟩
    · intro U V f hf
      refine ⟨hIso f, ?_⟩
      change #(PUnit.{u + 2}) ≤ κcov
      rw [mk_punit]
      exact Cardinal.one_le_aleph0.trans hκ
    · intro 𝒰 h𝒰 𝒱 h𝒱 htargets
      choose h𝒱cov h𝒱card using h𝒱
      exact ⟨hComp 𝒰 h𝒰.1 𝒱 h𝒱cov htargets, hsig h𝒰.2 h𝒱card⟩
    · intro 𝒰 h𝒰 V g
      obtain ⟨P, p₁, p₂, hp, hcov⟩ := hBC 𝒰 h𝒰.1 V g
      exact ⟨P, p₁, p₂, hp, hcov, h𝒰.2⟩
  let C : AlgebraicGeometry.BigFppfSite :=
    { initialSchemes := ∅
      initialSchemes_small := inferInstance
      cutoff := κ
      aleph0_lt_cutoff := B.aleph0_lt_cutoff.trans hBκ
      cutoff_isStrongPrelimit := hstrong
      aleph0_lt_cutoff_cof := hcof
      initialSchemes_mem := by simp
      initialCoverings := Cov₀
      initialCoverings_small := inferInstance
      initialCoverings_supported := by simp [Cov₀]
      coveringBound := κcov
      coveringOrdinal := α
      coveringOrdinal_isSuccLimit := hα
      initialCoverings_mem := by simp [Cov₀]
      coverings_isSite := hbsite
      fppf_has_representative := hrep' }
  exact ⟨C, hBκ.le, (le_max_right _ _).trans (le_max_right _ _), hlam⟩

end AlgebraicGeometry

end
