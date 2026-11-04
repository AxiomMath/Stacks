module

public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupAffine.Basic

/-!
# `K'₀(X)` is not the zero group

The Grothendieck group `AlgebraicGeometry.CoherentKZero` of coherent modules (Stacks 0FDG (2))
is nonzero on the spectrum of a field, and in particular on `Spec ℚ`.

## Main results

* `Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_finrankKPrime0Hom`: over a field,
  `finrank` descends to a homomorphism `K'₀(k) →+ ℤ`.
* `Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_ne_zero_kPrime0`: `K'₀(k) ≠ 0`.
* `Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_ne_zero_coherentKZero_spec`:
  `K'₀(Spec k) ≠ 0`.
* `Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_ne_zero_coherentKZero_specRat`:
  `K'₀(Spec ℚ) ≠ 0`.

## References

* [Stacks Project, Tag 0FDG](https://stacks.math.columbia.edu/tag/0FDG)
* [Stacks Project, Tag 0FDH](https://stacks.math.columbia.edu/tag/0FDH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Module

universe u

namespace Stacks.AlgebraicGeometry.GrothendieckGroupAffine

/-- **`finrank` as a homomorphism `K'₀(k) →+ ℤ`**: for a field `k`, there is a homomorphism
`K'₀(k) →+ ℤ` sending the class of every finite `k`-module to its dimension. -/
theorem exists_finrankKPrime0Hom (k : Type u) [Field k] :
    ∃ φ : KPrime0 k →+ ℤ,
      ∀ N : FinModule k, φ N.cls = (finrank k N.carrier : ℤ) := by
  refine KPrime0.universalProperty_existence
    (fun N : FinModule k => (finrank k N.carrier : ℤ)) ?_ ?_
  · intro N N' e
    exact congrArg (Nat.cast : ℕ → ℤ) e.finrank_eq
  · intro N N' N'' f g hf hg hexact
    have hrn : finrank k (LinearMap.range g) + finrank k (LinearMap.ker g)
        = finrank k N.carrier := LinearMap.finrank_range_add_finrank_ker g
    have hran : finrank k (LinearMap.range g) = finrank k N''.carrier := by
      rw [LinearMap.range_eq_top.mpr hg, finrank_top]
    have hker : finrank k (LinearMap.ker g) = finrank k N'.carrier := by
      rw [← hexact]
      exact ((LinearEquiv.ofInjective f hf).finrank_eq).symm
    rw [hran, hker] at hrn
    lia

/-- **`K'₀(k)` is nonzero** for every field `k`. -/
theorem exists_ne_zero_kPrime0 (k : Type u) [Field k] : ∃ x : KPrime0 k, x ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_finrankKPrime0Hom k
  refine ⟨({ carrier := k } : FinModule k).cls, fun h => ?_⟩
  have h1 : φ (({ carrier := k } : FinModule k).cls) = 1 := by simp [hφ]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- **`K'₀(Spec k) = K₀(Coh(𝒪_{Spec k}))` is nonzero** for every field `k`. -/
theorem exists_ne_zero_coherentKZero_spec (k : Type u) [Field k] :
    ∃ x : AlgebraicGeometry.CoherentKZero (Spec (CommRingCat.of k)), x ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_ne_zero_kPrime0 k
  refine ⟨(affineCoherentKZeroEquiv k).symm y, fun h => hy ?_⟩
  have := congrArg (affineCoherentKZeroEquiv k) h
  rwa [AddEquiv.apply_symm_apply, map_zero] at this

/-- **`K'₀(Spec ℚ)` is nonzero.** -/
theorem exists_ne_zero_coherentKZero_specRat :
    ∃ x : AlgebraicGeometry.CoherentKZero (Spec (CommRingCat.of ℚ)), x ≠ 0 :=
  exists_ne_zero_coherentKZero_spec ℚ

end Stacks.AlgebraicGeometry.GrothendieckGroupAffine

end
