module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.AwayRing

/-!
# Lifting homogeneous elements along a degreewise localization

Let `φ : 𝒜 →+*ᵍ ℬ` be a degreewise localization away from a degree-zero element `g` of `𝒜`
(`Stacks.GradedLocalization.IsAwayDegreewise`). The defining hypothesis says that a homogeneous
element of `ℬ` becomes the image of a homogeneous element of `𝒜` of the same degree after
multiplication by some power of `φ g`. This file proves two refinements: one power works for
two given homogeneous elements at once, and the power may be taken at least as large as a
prescribed exponent.

## Main results

* `Stacks.GradedLocalization.IsAwayDegreewise.exists_common_pow_mul_eq_map`: two homogeneous
  elements of `ℬ` are images of homogeneous elements of `𝒜` of the same degrees after
  multiplication by one common power of `φ g`.
* `Stacks.GradedLocalization.IsAwayDegreewise.exists_pow_mul_eq_map_of_mem`: a single homogeneous
  element of `ℬ` is such an image after multiplication by a power of `φ g` whose exponent is at
  least any prescribed bound.
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

/-- If `f m₀ = f g ^ k₀ * m` for a homogeneous `m₀`, then the same holds for every larger exponent,
with `m₀` replaced by a homogeneous element of the same degree. -/
private theorem exists_mem_eq_map_of_le {F : Type*} [FunLike F A B] [RingHomClass F A B] (f : F)
    (hg : g ∈ 𝒜 0) {d k₀ k : ℕ} {m : B} {m₀ : A} (hm₀ : m₀ ∈ 𝒜 d)
    (heq : f m₀ = f g ^ k₀ * m) (hk : k₀ ≤ k) :
    ∃ m' : A, m' ∈ 𝒜 d ∧ f m' = f g ^ k * m := by
  refine ⟨m₀ * g ^ (k - k₀), ?_, ?_⟩
  · simpa using SetLike.mul_mem_graded hm₀ (SetLike.pow_mem_graded (k - k₀) hg)
  · rw [map_mul, map_pow, heq, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hk]

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- Two homogeneous elements of `ℬ` are simultaneously images of homogeneous elements of `𝒜` of
the same degrees, after multiplication by one common power of `φ g`. -/
public theorem exists_common_pow_mul_eq_map (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    {d e : ℕ} {m s : B} (hm : m ∈ ℬ d) (hs : s ∈ ℬ e) :
    ∃ (m' s' : A) (i : ℕ), m' ∈ 𝒜 d ∧ s' ∈ 𝒜 e ∧
      φ m' = φ g ^ i * m ∧ φ s' = φ g ^ i * s := by
  obtain ⟨i₁, m₁, hm₁, hm₁eq⟩ := h.surj d m hm
  obtain ⟨i₂, s₁, hs₁, hs₁eq⟩ := h.surj e s hs
  obtain ⟨m', hm', hm'eq⟩ := exists_mem_eq_map_of_le φ hg hm₁ hm₁eq (le_max_left i₁ i₂)
  obtain ⟨s', hs', hs'eq⟩ := exists_mem_eq_map_of_le φ hg hs₁ hs₁eq (le_max_right i₁ i₂)
  exact ⟨m', s', _, hm', hs', hm'eq, hs'eq⟩

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- A single homogeneous element of `ℬ` is the image of a homogeneous element of `𝒜` of the same
degree after multiplication by a power `φ g ^ k` with `k` at least any prescribed `i`. -/
public theorem exists_pow_mul_eq_map_of_mem (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    {d : ℕ} {m : B} (hm : m ∈ ℬ d) (i : ℕ) :
    ∃ (k : ℕ) (m' : A), m' ∈ 𝒜 d ∧ i ≤ k ∧ φ m' = φ g ^ k * m := by
  obtain ⟨k₀, m₀, hm₀, hm₀eq⟩ := h.surj d m hm
  obtain ⟨m', hm', hm'eq⟩ := exists_mem_eq_map_of_le φ hg hm₀ hm₀eq (le_max_left k₀ i)
  exact ⟨_, m', hm', le_max_right k₀ i, hm'eq⟩

end IsAwayDegreewise

end Stacks.GradedLocalization

end
