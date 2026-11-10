module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular

/-!
# A complete regular local ring of characteristic `p` has a Frobenius splitting

Let `R` be a ring of characteristic `p`. A `p⁻¹`-linear map `θ : R → R` is an additive map with
`θ(aᵖ z) = a θ(z)`; it is an `R`-linear map `F_*R ⟶ R`, and it splits the Frobenius when
`θ(1) = 1`. This file constructs such a splitting for

* a field `k`: a `kᵖ`-linear retraction of `k` onto `kᵖ` followed by the inverse of the
  Frobenius `k ≃ kᵖ`;
* a power series ring `k[[x_σ]]`: `θ(z)` has as coefficient of `xᵐ` the image under the
  splitting of `k` of the coefficient of `x^{p m}` in `z`;
* a complete regular local ring containing a field, through the Cohen structure theorem
  ([Stacks, Tag 0C0S]).

No finiteness of `k` over `kᵖ` is assumed. This is the input of the Frobenius route to
[Stacks, Tag 0B4U] that uses completeness: over a complete regular local ring `A` of
characteristic `p` there is a nonzero `A`-linear map `F_*A ⟶ A` even when `A` is not finite over
`Aᵖ`.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_field`.
* `Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_mvPowerSeries`.
* `Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_of_isRegularLocalRing`.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
* [Stacks Project, Tag 0C0S](https://stacks.math.columbia.edu/tag/0C0S)
-/

@[expose] public section

open MvPowerSeries

namespace Stacks.ResolutionOfSurfaces

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The Frobenius of a field of characteristic `p` splits.** Writing `kᵖ` for the image of
the Frobenius, a `kᵖ`-linear retraction `P : k → kᵖ` of the inclusion composed with the inverse
of `k ≃ kᵖ` is additive, satisfies `π(aᵖ z) = a π(z)`, and sends `1` to `1`. -/
theorem exists_frobeniusSplitting_field (k : Type*) [Field k] [CharP k p] :
    ∃ π : k →+ k, (∀ a z, π (a ^ p * z) = a * π z) ∧ π 1 = 1 := by
  let F : Subfield k := (frobenius k p).fieldRange
  let ι : F →ₗ[F] k := Algebra.linearMap F k
  have hι : LinearMap.ker ι = ⊥ :=
    LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F k)
  obtain ⟨P, hP⟩ := ι.exists_leftInverse_of_injective hι
  let e : k ≃+* F :=
    RingEquiv.ofBijective (frobenius k p).rangeRestrictField
      (frobenius k p).rangeRestrictField_bijective
  have he : ∀ a : k, ((e a : F) : k) = a ^ p := fun a => rfl
  have h1 : P 1 = 1 := by
    have := LinearMap.congr_fun hP 1
    simpa [ι] using this
  let π : k →+ k :=
    { toFun := fun z => e.symm (P z)
      map_zero' := by simp
      map_add' := fun z z' => by simp }
  refine ⟨π, fun a z => ?_, ?_⟩
  · have hz : a ^ p * z = (e a) • z := by rw [Subfield.smul_def, he, smul_eq_mul]
    change e.symm (P (a ^ p * z)) = a * e.symm (P z)
    rw [hz, P.map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
  · change e.symm (P 1) = 1
    rw [h1, map_one]

/-- The terms of `∑_{x ∈ antidiagonal (p m)} wᵖ_{x₁} z_{x₂}` with `x₁` not divisible by `p`
vanish, and the others are indexed by `antidiagonal m`. -/
theorem coeff_frobenius_mul_smul {σ k : Type*} [DecidableEq σ] [CommRing k] [CharP k p]
    (w z : MvPowerSeries σ k) (m : σ →₀ ℕ) :
    coeff (p • m) (w ^ p * z) =
      ∑ y ∈ Finset.antidiagonal m, coeff y.1 w ^ p * coeff (p • y.2) z := by
  classical
  have hp0 : p ≠ 0 := hp.out.ne_zero
  rw [← map_frobenius_expand p hp0, coeff_mul]
  let j : (σ →₀ ℕ) × (σ →₀ ℕ) ↪ (σ →₀ ℕ) × (σ →₀ ℕ) :=
    ⟨fun y => (p • y.1, p • y.2), fun y y' h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (nsmul_right_injective hp0 h.1) (nsmul_right_injective hp0 h.2)⟩
  have hsub : (Finset.antidiagonal m).map j ⊆ Finset.antidiagonal (p • m) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [Finset.mem_antidiagonal] at hy ⊢
    change p • y.1 + p • y.2 = p • m
    rw [← smul_add, hy]
  rw [← Finset.sum_subset hsub, Finset.sum_map]
  · refine Finset.sum_congr rfl fun y _ => ?_
    change coeff (p • y.1) (map (frobenius k p) (expand p hp0 w)) * coeff (p • y.2) z = _
    rw [coeff_map, coeff_expand_smul, frobenius_def]
  · intro x hx hxj
    rw [coeff_map]
    by_cases hdvd : ∀ i, p ∣ x.1 i
    · exfalso
      apply hxj
      rw [Finset.mem_antidiagonal] at hx
      have hdvd2 : ∀ i, p ∣ x.2 i := by
        intro i
        have hi := congrArg (fun f => f i) hx
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hi
        exact (Nat.dvd_add_right (hdvd i)).mp (hi ▸ dvd_mul_right p (m i))
      let d : (σ →₀ ℕ) → (σ →₀ ℕ) := fun a => Finsupp.mapRange (· / p) (Nat.zero_div p) a
      have hd : ∀ a : σ →₀ ℕ, (∀ i, p ∣ a i) → p • d a = a := by
        intro a ha
        ext i
        simp [d, Nat.mul_div_cancel' (ha i)]
      refine Finset.mem_map.mpr ⟨(d x.1, d x.2), ?_, ?_⟩
      · rw [Finset.mem_antidiagonal]
        apply nsmul_right_injective hp0
        change p • (d x.1 + d x.2) = p • m
        rw [smul_add, hd _ hdvd, hd _ hdvd2, hx]
      · change (p • d x.1, p • d x.2) = x
        rw [hd _ hdvd, hd _ hdvd2]
    · push Not at hdvd
      obtain ⟨i, hi⟩ := hdvd
      rw [coeff_expand_of_not_dvd p hp0 w hi, map_zero, zero_mul]

/-- **A power series ring over a field of characteristic `p` has a Frobenius splitting**:
`θ(z)ₘ = π(z_{p m})` for a splitting `π` of the Frobenius of the coefficient field. -/
theorem exists_frobeniusSplitting_mvPowerSeries (σ k : Type*) [Field k] [CharP k p] :
    ∃ θ : MvPowerSeries σ k →+ MvPowerSeries σ k,
      (∀ a z, θ (a ^ p * z) = a * θ z) ∧ θ 1 = 1 := by
  classical
  obtain ⟨π, hπ, hπ1⟩ := exists_frobeniusSplitting_field p k
  let θ : MvPowerSeries σ k →+ MvPowerSeries σ k :=
    { toFun := fun z m => π (coeff (p • m) z)
      map_zero' := by funext m; change π (coeff (p • m) 0) = 0; simp
      map_add' := fun z z' => by
        funext m; change π (coeff (p • m) (z + z')) = π (coeff (p • m) z) + π (coeff (p • m) z')
        simp }
  have hθ : ∀ z m, coeff m (θ z) = π (coeff (p • m) z) := fun _ _ => rfl
  refine ⟨θ, fun a z => ?_, ?_⟩
  · ext m
    rw [hθ, coeff_frobenius_mul_smul, map_sum, coeff_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hπ, hθ]
  · ext m
    rw [hθ, coeff_one, coeff_one]
    by_cases hm : m = 0
    · simp [hm, hπ1]
    · simp [hm, hp.out.ne_zero]

/-- **A complete regular local ring of characteristic `p` has a Frobenius splitting**: an
additive `θ : R → R` with `θ(aᵖ z) = a θ(z)` and `θ(1) = 1`. By the Cohen structure theorem
([Stacks, Tag 0C0S]) `R` is a power series ring over its residue field, which has one by
`Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_mvPowerSeries`. -/
theorem exists_frobeniusSplitting_of_isRegularLocalRing (R : Type*) [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CharP R p] :
    ∃ θ : R →+ R, (∀ a z, θ (a ^ p * z) = a * θ z) ∧ θ 1 = 1 := by
  let : Algebra (ZMod p) R := ZMod.algebra R p
  obtain ⟨e⟩ :=
    (IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries.{_, 0, 0} R _ rfl).1 (ZMod p)
  have : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_injective_ringHom
      ((algebraMap R (IsLocalRing.ResidueField R)).comp (algebraMap (ZMod p) R)).injective p
  obtain ⟨θ, hθ, hθ1⟩ := exists_frobeniusSplitting_mvPowerSeries p (Fin _)
    (IsLocalRing.ResidueField R)
  let θR : R →+ R :=
    { toFun := fun z => e.symm (θ (e z))
      map_zero' := by simp
      map_add' := fun z z' => by simp }
  refine ⟨θR, fun a z => ?_, ?_⟩
  · change e.symm (θ (e (a ^ p * z))) = a * e.symm (θ (e z))
    rw [map_mul, map_pow, hθ, map_mul, RingEquiv.symm_apply_apply]
  · change e.symm (θ (e 1)) = 1
    rw [map_one, hθ1, map_one]

end Stacks.ResolutionOfSurfaces

end
