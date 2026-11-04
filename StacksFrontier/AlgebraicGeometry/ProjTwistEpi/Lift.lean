module

public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualSurjective

/-!
# Lifting a homogeneous fraction of arbitrary degree past the surjectivity bound

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is surjective on
homogeneous components of all degrees `≥ N`. A fraction `b / s` with `b` of twisted degree `k`
and `s` of degree `k` — that is, a local representative of a section of the `n`-th twist of the
structure sheaf of `Proj ℬ` — need not have either of `b`, `s` in the image of `ψ`, because `k`
may be small. Multiplying numerator and denominator by one and the same power of a homogeneous
element `g` of positive degree raises both degrees past `N` without changing the fraction, and
then both are in the image.

This is the degree-`n` analogue of
`Stacks.AlgebraicGeometry.RelativeProjChain.surjective_awayMap_of_eventually_surjective`, which
is the degree-zero case phrased as surjectivity of `𝒜_{(f)} → ℬ_{(ψ f)}`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistEpi.exists_lift_twistGrading`: the lifting statement, with
  the exponent and the common degree existentially quantified.
* `Stacks.AlgebraicGeometry.ProjTwistEpi.mem_homogeneous_of_mem_integerGrading` and
  `Stacks.AlgebraicGeometry.ProjTwistEpi.mem_integerGrading_of_mem_homogeneous`: the two
  translations between the `ℤ`-extended grading and the honest homogeneous components, in
  nonnegative degree.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjTwistEpi

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [GradedRing ℬ] in
/-- Membership in the `ℤ`-extended grading, read as membership in an honest homogeneous
component once the index is known to be nonnegative. -/
public theorem mem_homogeneous_of_mem_integerGrading {i : ℤ} (hi : 0 ≤ i) {b : B}
    (hb : b ∈ integerGrading (S := B) ℬ i) : b ∈ ℬ i.toNat := by
  rwa [show i = (i.toNat : ℤ) by omega, integerGrading_natCast,
    mem_homogeneousSubmodule] at hb

omit [GradedRing ℬ] in
/-- Membership in an honest homogeneous component, read as membership in the `ℤ`-extended
grading. -/
public theorem mem_integerGrading_of_mem_homogeneous {i : ℤ} (hi : 0 ≤ i) {b : B}
    (hb : b ∈ ℬ i.toNat) : b ∈ integerGrading (S := B) ℬ i := by
  rwa [show i = (i.toNat : ℤ) by omega, integerGrading_natCast, mem_homogeneousSubmodule]

omit [GradedRing 𝒜] in
/-- **Lifting a twist fraction past the surjectivity bound.** Let `ψ` be surjective on
homogeneous components of all degrees `≥ N`, let `b` be a numerator of twisted degree `k` and
`s` a denominator of degree `k`, and let `g` be homogeneous of positive degree `m`. Then
numerator and denominator can both be multiplied by one and the same power of `g` so that the
results lift along `ψ`, the lifts being again a numerator and a denominator of one common
degree. -/
public theorem exists_lift_twistGrading (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Surjective (GradedRingHom.gradedAddHom ψ d))
    (n : ℤ) {k : ℕ} {b s : B} (hb : b ∈ twistGrading (S := B) ℬ n (k : ℤ)) (hs : s ∈ ℬ k)
    {m : ℕ} (hm : 0 < m) {g : B} (hg : g ∈ ℬ m) :
    ∃ (j K : ℕ) (β t : A), β ∈ twistGrading (S := A) 𝒜 n (K : ℤ) ∧ t ∈ 𝒜 K ∧
      ψ β = b * g ^ j ∧ ψ t = s * g ^ j := by
  have hNm : N ≤ N * m := Nat.le_mul_of_pos_right N hm
  have hpow : g ^ N ∈ ℬ (N * m) := by
    simpa only [smul_eq_mul] using SetLike.pow_mem_graded N hg
  obtain ⟨t, ht, hte⟩ := Stacks.AlgebraicGeometry.RelativeProjChain.exists_mem_map_eq
    𝒜 ℬ ψ hN (hNm.trans (Nat.le_add_left (N * m) k)) (SetLike.mul_mem_graded hs hpow)
  by_cases hkn : 0 ≤ (k : ℤ) + n
  · have hb' : b ∈ ℬ ((k : ℤ) + n).toNat :=
      mem_homogeneous_of_mem_integerGrading ℬ hkn (by simpa only [twistGrading_apply] using hb)
    obtain ⟨β, hβ, hβe⟩ := Stacks.AlgebraicGeometry.RelativeProjChain.exists_mem_map_eq
      𝒜 ℬ ψ hN (hNm.trans (Nat.le_add_left (N * m) _)) (SetLike.mul_mem_graded hb' hpow)
    refine ⟨N, k + N * m, β, t, ?_, ht, hβe, hte⟩
    have hdeg : (((k + N * m : ℕ) : ℤ) + n).toNat = ((k : ℤ) + n).toNat + N * m := by omega
    rw [twistGrading_apply]
    refine mem_integerGrading_of_mem_homogeneous 𝒜 (by omega) ?_
    rwa [hdeg]
  · have hb0 : b = 0 := by
      rw [twistGrading_apply, integerGrading_neg ℬ _ (by omega)] at hb
      simpa using hb
    refine ⟨N, k + N * m, 0, t, zero_mem _, ht, ?_, hte⟩
    rw [hb0, zero_mul, map_zero]

end Stacks.AlgebraicGeometry.ProjTwistEpi

end
