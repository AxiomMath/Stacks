module

public import StacksFrontier.AlgebraicGeometry.ProjAwayBaseChange.Basic

/-!
# Injectivity and surjectivity criteria for a map of homogeneous away-localizations

Let `g : 𝒜 →+*ᵍ ℬ` be a homomorphism of graded rings and let `f ∈ 𝒜 d` be homogeneous. The
degree-zero part of the localization away from `f` is `HomogeneousLocalization.Away 𝒜 f`, whose
elements are the fractions `a / f ^ n` with `a ∈ 𝒜 (n • d)`, and `g` induces
`HomogeneousLocalization.Away.map g f : Away 𝒜 f →+* Away ℬ (g f)`. This file gives criteria,
in terms of homogeneous elements of the degrees `n • d`, for this map to be injective or
surjective, the graded analogues of `IsLocalization.Away.map_injective_iff` and
`IsLocalization.Away.map_surjective_iff`.

## Main results

* `Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff`: a fraction
  `a / f ^ n` lies in the kernel of the induced map exactly when `f ^ k * a` lies in the kernel
  of `g` for some `k`.
* `Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMap_injective_iff`: the induced map is
  injective exactly when every homogeneous `a` of a degree `n • d` with `g a = 0` is killed by a
  power of `f`.
* `Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMap_surjective_iff`: the induced map is
  surjective exactly when, for every `b ∈ ℬ (n • d)`, some `g f ^ k * b` is the image of an
  element of `𝒜 ((k + n) • d)`.
-/

@[expose] public section

open HomogeneousLocalization

namespace Stacks.AlgebraicGeometry.HomogeneousAwayMap

variable {ι A σ B τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → σ} [GradedRing 𝒜]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ι → τ} [GradedRing ℬ]

/-- A fraction `a / f ^ n` lies in the kernel of `HomogeneousLocalization.Away.map g f` if and
only if `f ^ k * a` lies in the kernel of `g` for some `k`. -/
public theorem awayMk_mem_ker_awayMap_iff (g : 𝒜 →+*ᵍ ℬ) {d : ι} {f : A} (hf : f ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    HomogeneousLocalization.Away.mk 𝒜 hf n a ha ∈
        RingHom.ker (HomogeneousLocalization.Away.map g f) ↔
      ∃ k : ℕ, f ^ k * a ∈ RingHom.ker (g : A →+* B) := by
  rw [RingHom.mem_ker, Away.map_mk,
    ProjAwayBaseChange.awayMk_eq_zero_iff ℬ (g.map_mem hf) n (g a) (g.map_mem ha)]
  simp only [RingHom.mem_ker, map_mul, map_pow, RingHom.coe_coe,
    GradedRingHom.coe_toRingHom]

/-- The graded analogue of `IsLocalization.Away.map_injective_iff`: for a homomorphism
`g : 𝒜 →+*ᵍ ℬ` of graded rings and a homogeneous `f ∈ 𝒜 d`, the induced map
`HomogeneousLocalization.Away 𝒜 f →+* HomogeneousLocalization.Away ℬ (g f)` is injective exactly
when every homogeneous element of a degree `n • d` killed by `g` is killed by a power of `f`. -/
public theorem awayMap_injective_iff (g : 𝒜 →+*ᵍ ℬ) {d : ι} {f : A} (hf : f ∈ 𝒜 d) :
    Function.Injective (HomogeneousLocalization.Away.map g f) ↔
      ∀ (n : ℕ) (a : A), a ∈ 𝒜 (n • d) → g a = 0 → ∃ m : ℕ, f ^ m * a = 0 := by
  constructor
  · intro H n a ha hga
    refine (ProjAwayBaseChange.awayMk_eq_zero_iff 𝒜 hf n a ha).mp (H ?_)
    rw [map_zero]
    exact (awayMk_mem_ker_awayMap_iff g hf n a ha).mpr ⟨0, by simp [hga]⟩
  · intro H
    refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
    obtain ⟨k, hk⟩ := (awayMk_mem_ker_awayMap_iff g hf n a ha).mp hz
    have hmem : f ^ k * a ∈ 𝒜 ((k + n) • d) := by
      rw [add_smul]
      exact SetLike.mul_mem_graded (SetLike.pow_mem_graded k hf) ha
    obtain ⟨m, hm⟩ := H (k + n) (f ^ k * a) hmem hk
    refine (ProjAwayBaseChange.awayMk_eq_zero_iff 𝒜 hf n a ha).mpr ⟨m + k, ?_⟩
    rw [pow_add, mul_assoc, hm]

/-- The graded analogue of `IsLocalization.Away.map_surjective_iff`: for a homomorphism
`g : 𝒜 →+*ᵍ ℬ` of graded rings and a homogeneous `f ∈ 𝒜 d`, the induced map
`HomogeneousLocalization.Away 𝒜 f →+* HomogeneousLocalization.Away ℬ (g f)` is surjective exactly
when, for every homogeneous `b ∈ ℬ (n • d)`, some multiple `g f ^ k * b` lies in the image of the
homogeneous component `𝒜 ((k + n) • d)`. -/
public theorem awayMap_surjective_iff (g : 𝒜 →+*ᵍ ℬ) {d : ι} {f : A} (hf : f ∈ 𝒜 d) :
    Function.Surjective (HomogeneousLocalization.Away.map g f) ↔
      ∀ (n : ℕ) (b : B), b ∈ ℬ (n • d) →
        ∃ (k : ℕ) (a : A), a ∈ 𝒜 ((k + n) • d) ∧ g a = g f ^ k * b := by
  constructor
  · intro H n b hb
    obtain ⟨z, hz⟩ := H (Away.mk ℬ (g.map_mem hf) n b hb)
    obtain ⟨m, x, hx, rfl⟩ := Away.mk_surjective 𝒜 hf z
    rw [Away.map_mk] at hz
    obtain ⟨j, hj⟩ :=
      (ProjAwayBaseChange.awayMk_eq_iff ℬ (g.map_mem hf) m n (g x) b (g.map_mem hx) hb).mp hz
    refine ⟨j + m, f ^ (j + n) * x, ?_, ?_⟩
    · have hdeg : (j + n) • d + m • d = (j + m + n) • d := by
        rw [← add_smul]; congr 1; lia
      exact hdeg ▸ SetLike.mul_mem_graded (SetLike.pow_mem_graded (j + n) hf) hx
    · simp only [map_mul, map_pow, GradedRingHom.coe_toRingHom] at hj ⊢
      rw [← mul_assoc, ← pow_add] at hj
      rw [hj, ← mul_assoc, ← pow_add]
  · intro H w
    obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (g.map_mem hf) w
    obtain ⟨k, a, ha, hga⟩ := H n b hb
    refine ⟨Away.mk 𝒜 hf (k + n) a ha, ?_⟩
    rw [Away.map_mk,
      ProjAwayBaseChange.awayMk_eq_iff ℬ (g.map_mem hf) (k + n) n (g a) b (g.map_mem ha) hb]
    refine ⟨0, ?_⟩
    simp only [GradedRingHom.coe_toRingHom, pow_zero, one_mul, hga, pow_add]
    ring

end Stacks.AlgebraicGeometry.HomogeneousAwayMap
