module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.AwayLocalization

/-!
# A degreewise localization of graded rings is a localization

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is, in each degree,
the localization away from a degree-zero element `g` of `𝒜`
(`Stacks.GradedLocalization.IsAwayDegreewise`). This file upgrades that degreewise hypothesis to
the ungraded statement: `ℬ` is the localization of `𝒜` away from `g`.

## Main results

* `Stacks.GradedLocalization.IsAwayDegreewise.isLocalization_away`: `ℬ` is `𝒜` localized away
  from `g`.
-/

@[expose] public section

open HomogeneousLocalization

universe u

namespace Stacks.GradedLocalization

variable {A B : Type u} {σ τ : Type*}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {φ : 𝒜 →+*ᵍ ℬ} {g : A}

namespace IsAwayDegreewise

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- Every element of `ℬ`, not only every homogeneous one, becomes the image of an element of `𝒜`
after multiplication by a power of the image of `g`. -/
public theorem exists_pow_mul_eq_map (h : IsAwayDegreewise φ g) (y : B) :
    ∃ (k : ℕ) (x : A), φ x = φ g ^ k * y := by
  classical
  choose k x _ hxy using fun i => h.surj i _ (DirectSum.decompose ℬ y i).2
  refine ⟨(DirectSum.decompose ℬ y).support.sup k,
    ∑ i ∈ (DirectSum.decompose ℬ y).support,
      x i * g ^ ((DirectSum.decompose ℬ y).support.sup k - k i), ?_⟩
  calc φ (∑ i ∈ (DirectSum.decompose ℬ y).support,
          x i * g ^ ((DirectSum.decompose ℬ y).support.sup k - k i))
      = ∑ i ∈ (DirectSum.decompose ℬ y).support,
          φ g ^ (DirectSum.decompose ℬ y).support.sup k *
            ((DirectSum.decompose ℬ y i : ℬ i) : B) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [map_mul, map_pow, hxy i, mul_right_comm, ← pow_add,
          Nat.add_sub_cancel' (Finset.le_sup (f := k) hi)]
    _ = φ g ^ (DirectSum.decompose ℬ y).support.sup k * y := by
      rw [← Finset.mul_sum, DirectSum.sum_support_decompose ℬ y]

/-- An element of `𝒜` killed by `φ`, not only a homogeneous one, is killed by a power of `g`. -/
public theorem exists_pow_mul_eq_zero (h : IsAwayDegreewise φ g) {a : A} (ha : φ a = 0) :
    ∃ k : ℕ, g ^ k * a = 0 := by
  classical
  choose k hk using fun i => h.torsion i _ (DirectSum.decompose 𝒜 a i).2 (by simp [ha])
  refine ⟨(DirectSum.decompose 𝒜 a).support.sup k, ?_⟩
  nth_rw 2 [← DirectSum.sum_support_decompose 𝒜 a]
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Nat.add_sub_cancel' (Finset.le_sup (f := k) hi), pow_add, mul_assoc, mul_left_comm,
    hk i, mul_zero]

/-- **A degreewise localization is a localization.** If `φ` is, in each degree, the localization
of `𝒜` away from the degree-zero element `g`, then `ℬ` is the localization of `𝒜` away from
`g`. -/
public theorem isLocalization_away (h : IsAwayDegreewise φ g) :
    letI := φ.toRingHom.toAlgebra
    IsLocalization.Away g B := by
  let := φ.toRingHom.toAlgebra
  have halg : ∀ a : A, algebraMap A B a = φ a := fun _ => rfl
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, n, rfl⟩
    rw [halg, map_pow]
    exact h.isUnit_map.pow n
  · intro z
    obtain ⟨k, a, hak⟩ := h.exists_pow_mul_eq_map z
    refine ⟨⟨a, ⟨g ^ k, k, rfl⟩⟩, ?_⟩
    rw [halg, halg, map_pow, hak]
    ring
  · intro a a' haa'
    rw [halg, halg] at haa'
    obtain ⟨k, hk⟩ := h.exists_pow_mul_eq_zero (by rw [map_sub, haa', sub_self] :
      φ (a - a') = 0)
    exact ⟨⟨g ^ k, k, rfl⟩, by simpa [mul_sub, sub_eq_zero] using hk⟩

end IsAwayDegreewise

end Stacks.GradedLocalization

end
