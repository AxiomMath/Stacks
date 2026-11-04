module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusReconstruction

/-!
# The Frobenius reconstruction identity on the fraction field

Let `A ⊆ B` be domains with fraction fields `K ⊆ L`, let `ρ : B → A` lift the `p`-th power map, and
let `θ_K : K → K` be additive with `θ_K(aᵖ x) = a θ_K(x)` extending `θ : A → A`. If
`c s = ∑ᵢ θ(ρ(bᵢ) ρ(s)) βᵢ` for every `s ∈ B`
(`Stacks.ResolutionOfSurfaces.exists_smul_eq_sum_frobenius`), then for every `σ ∈ L`

  `c σ = ∑ᵢ θ_K((bᵢ σ)ᵖ) βᵢ`,

where `(bᵢ σ)ᵖ ∈ K` because `Lᵖ ⊆ K`. Indeed both sides are `K`-linear in `σ` and agree on `B`;
concretely `σ = s / t = s tᵖ⁻¹ / ρ(t)` with `ρ(t) ∈ A`.

This is the form in which the identity is used on the generic germs of sections in the Frobenius
route to [Stacks, Tag 0B4U].

## Main results

* `Stacks.ResolutionOfSurfaces.smul_eq_sum_frobeniusSplitting_fractionRing`: the identity above.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public section

namespace Stacks.ResolutionOfSurfaces

variable {p : ℕ} [hp : Fact p.Prime] {A B K L : Type*} [CommRing A] [IsDomain A] [CommRing B]
  [IsDomain B] [Algebra A B] [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]

omit [IsDomain A] in
/-- **The Frobenius reconstruction identity on the fraction field.** If
`c s = ∑ᵢ θ(ρ(bᵢ) ρ(s)) βᵢ` on `B`, and `θ_K` extends `θ` to `K` with `θ_K(aᵖ x) = a θ_K(x)`, then
`c σ = ∑ᵢ θ_K(kᵢ) βᵢ` for every `σ ∈ L`, where `kᵢ ∈ K` is `(bᵢ σ)ᵖ`. -/
theorem smul_eq_sum_frobeniusSplitting_fractionRing (ρ : B → A)
    (hρ : ∀ s, algebraMap A B (ρ s) = s ^ p) (θ : A →+ A) (θK : K →+ K)
    (hθK : ∀ a x, θK (a ^ p * x) = a * θK x)
    (hθKA : ∀ z, θK (algebraMap A K z) = algebraMap A K (θ z)) {n : ℕ} (c : A)
    (b β : Fin n → B) (hc : ∀ s : B, c • s = ∑ i, θ (ρ (b i) * ρ s) • β i) (σ : L)
    (k : Fin n → K) (hk : ∀ i, algebraMap K L (k i) = (algebraMap B L (b i) * σ) ^ p) :
    algebraMap A L c * σ = ∑ i, algebraMap K L (θK (k i)) * algebraMap B L (β i) := by
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp hAK
  have hAB : Function.Injective (algebraMap A B) := fun x y h =>
    hAL (by rw [IsScalarTower.algebraMap_apply A B L, h, ← IsScalarTower.algebraMap_apply])
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have ρmul : ∀ s t, ρ (s * t) = ρ s * ρ t := fun s t =>
    hAB (by rw [hρ, map_mul, hρ, hρ, mul_pow])
  have hρL : ∀ s, algebraMap A L (ρ s) = algebraMap B L s ^ p := fun s => by
    rw [IsScalarTower.algebraMap_apply A B L, hρ, map_pow]
  obtain ⟨s, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := B) σ
  have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
  have htL : algebraMap B L t ≠ 0 := fun h => ht0 (hBL (by rw [h, map_zero]))
  obtain ⟨a, ha⟩ : ∃ a, a = ρ t := ⟨_, rfl⟩
  have haL : algebraMap A L a = algebraMap B L t ^ p := by rw [ha]; exact hρL t
  have haL0 : algebraMap A L a ≠ 0 := by rw [haL]; exact pow_ne_zero _ htL
  obtain ⟨s', hs'⟩ : ∃ s', s' = s * t ^ (p - 1) := ⟨_, rfl⟩
  have hσ : algebraMap B L s / algebraMap B L t = algebraMap B L s' / algebraMap A L a := by
    rw [haL, hs', map_mul, map_pow, div_eq_div_iff htL (pow_ne_zero _ htL), mul_assoc,
      ← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
  -- the values of `θ_K` on the `kᵢ`
  have hki : ∀ i, k i = (algebraMap A K a)⁻¹ ^ p * algebraMap A K (ρ (b i * s')) := by
    intro i
    apply (algebraMap K L).injective
    have e1 : algebraMap K L ((algebraMap A K a)⁻¹ ^ p * algebraMap A K (ρ (b i * s'))) =
        (algebraMap A L a)⁻¹ ^ p * (algebraMap B L (b i) * algebraMap B L s') ^ p := by
      rw [map_mul, map_pow, map_inv₀, ← IsScalarTower.algebraMap_apply A K L,
        ← IsScalarTower.algebraMap_apply A K L, hρL, map_mul]
    rw [e1, hk i, hσ, div_eq_mul_inv]
    ring
  have hθk : ∀ i, algebraMap K L (θK (k i)) =
      (algebraMap A L a)⁻¹ * algebraMap A L (θ (ρ (b i) * ρ s')) := by
    intro i
    rw [hki, hθK, hθKA, ρmul, map_mul, map_inv₀, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K L]
  have hsum : algebraMap A L c * algebraMap B L s' =
      ∑ i, algebraMap A L (θ (ρ (b i) * ρ s')) * algebraMap B L (β i) := by
    have h := congrArg (algebraMap B L) (hc s')
    simp only [map_sum, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] at h
    exact h
  rw [Finset.sum_congr rfl fun i _ => by rw [hθk i], hσ]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← hsum]
  field_simp

end Stacks.ResolutionOfSurfaces

end
