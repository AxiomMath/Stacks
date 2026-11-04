module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic

/-! # Transporting a graded divided power structure along an algebra equivalence

Let `A` and `B` be nonnegatively graded `R`-algebras, both strictly graded commutative, and let
`e : A ≃ₐ[R] B` be an algebra equivalence which matches the two gradings. This file transports a
divided power structure on the positive even part of `A` to one on the positive even part of `B`,
by conjugation: `δₙ y = e (γₙ (e⁻¹ y))`.

A grading-preserving algebra equivalence matches the gradings exactly: if `e` carries `𝒜 m` into
`ℬ m` for every `m`, then it carries it onto `ℬ m`. The positive even part and the even part are
therefore matched as well.

The file also records the divided power structure carried by a graded algebra whose positive even
part is zero.

## Main definitions

* `DividedPowers.TateResolution.DividedPowerStructure.transport`: the transported structure.
* `DividedPowers.TateResolution.dividedPowerStructureOfPositiveEvenPartEqBot`: the structure on
  a graded algebra with vanishing positive even part.

## Main results

* `DividedPowers.TateResolution.map_grade_eq`: a grading-preserving algebra equivalence maps each
  homogeneous piece onto the corresponding one.
* `DividedPowers.TateResolution.mem_grade_iff_of_mapsTo`: the resulting membership criterion.
* `DividedPowers.TateResolution.mem_positiveEvenPart_equiv_iff` and
  `DividedPowers.TateResolution.mem_evenPart_equiv_iff`: the matching of the even parts.
* `DividedPowers.TateResolution.DividedPowerStructure.transport_dpow`: the defining formula.
* `DividedPowers.TateResolution.IsCompatibleWithDifferential.transport`: compatibility with a
  differential transports along the equivalence.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open DirectSum

universe u v w

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

section Grading

variable (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- A grading-preserving algebra equivalence maps each homogeneous piece *onto* the homogeneous
piece of the same degree. -/
public theorem map_grade_eq (e : A ≃ₐ[R] B)
    (he : ∀ (m : ℕ) (x : A), x ∈ 𝒜 m → e x ∈ ℬ m) (m : ℕ) :
    (𝒜 m).map e.toLinearMap = ℬ m := by
  classical
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact he m x hx
  · intro y hy
    set x := e.symm y with hxdef
    set s := (DirectSum.decompose 𝒜 x).support with hs
    set z : ℕ → A := fun i ↦ (DirectSum.decompose 𝒜 x i : A) with hzdef
    have hz : ∀ i, z i ∈ 𝒜 i := fun i ↦ (DirectSum.decompose 𝒜 x i).property
    have hxsum : x = ∑ i ∈ s, z i := (DirectSum.sum_support_decompose 𝒜 x).symm
    have hysum : y = ∑ i ∈ s, e (z i) := by
      rw [show y = e x by rw [hxdef, e.apply_symm_apply], hxsum, map_sum]
    have h1 : GradedRing.proj ℬ m y = y := by
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same ℬ hy]
    have hzero : ∀ i, i ≠ m → GradedRing.proj ℬ m (e (z i)) = 0 := by
      intro i hne
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne ℬ (he i (z i) (hz i)) hne]
    have h2 : y = ∑ i ∈ s, GradedRing.proj ℬ m (e (z i)) := by
      rw [← h1, hysum, map_sum]
    by_cases hm : m ∈ s
    · refine ⟨z m, hz m, ?_⟩
      rw [h2, Finset.sum_eq_single_of_mem m hm (fun i _ hne ↦ hzero i hne),
        GradedRing.proj_apply, DirectSum.decompose_of_mem_same ℬ (he m (z m) (hz m))]
      rfl
    · have h3 : y = 0 := by
        rw [h2, Finset.sum_eq_zero]
        intro i hi
        exact hzero i fun hq ↦ hm (hq ▸ hi)
      rw [h3]
      exact Submodule.zero_mem _

/-- Along a grading-preserving algebra equivalence, homogeneity of an element is equivalent to
homogeneity of its image. -/
public theorem mem_grade_iff_of_mapsTo (e : A ≃ₐ[R] B)
    (he : ∀ (m : ℕ) (x : A), x ∈ 𝒜 m → e x ∈ ℬ m) (m : ℕ) (x : A) :
    x ∈ 𝒜 m ↔ e x ∈ ℬ m := by
  refine ⟨he m x, fun hx ↦ ?_⟩
  rw [← map_grade_eq 𝒜 ℬ e he m] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rwa [show x = y from e.injective hxy.symm]

/-- A grading-matching algebra equivalence maps a supremum of homogeneous pieces onto the
supremum of the corresponding pieces. -/
private theorem map_iSup_grade_eq (e : A ≃ₐ[R] B)
    (he : ∀ (m : ℕ) (x : A), x ∈ 𝒜 m ↔ e x ∈ ℬ m) (s : ℕ → ℕ) :
    (⨆ d, 𝒜 (s d)).map e.toLinearMap = ⨆ d, ℬ (s d) := by
  rw [Submodule.map_iSup]
  exact iSup_congr fun d ↦ map_grade_eq 𝒜 ℬ e (fun m x hx ↦ (he m x).mp hx) (s d)

variable (e : A ≃ₐ[R] B) (he : ∀ (m : ℕ) (x : A), x ∈ 𝒜 m ↔ e x ∈ ℬ m)

include he

/-- Along a grading-matching algebra equivalence, the even parts correspond. -/
public theorem mem_evenPart_equiv_iff (y : B) :
    y ∈ evenPart ℬ ↔ e.symm y ∈ evenPart 𝒜 := by
  have hmap : (evenPart 𝒜).map e.toLinearMap = evenPart ℬ :=
    map_iSup_grade_eq 𝒜 ℬ e he fun d ↦ 2 * d
  rw [← hmap, Submodule.mem_map_equiv]
  rfl

/-- Along a grading-matching algebra equivalence, the positive even parts correspond. -/
public theorem mem_positiveEvenPart_equiv_iff (y : B) :
    y ∈ positiveEvenPart ℬ ↔ e.symm y ∈ positiveEvenPart 𝒜 := by
  have hmap : (positiveEvenPart 𝒜).map e.toLinearMap = positiveEvenPart ℬ :=
    map_iSup_grade_eq 𝒜 ℬ e he fun d ↦ 2 * (d + 1)
  rw [← hmap, Submodule.mem_map_equiv]
  rfl

end Grading

section Transport

variable {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable [IsStrictlyGradedComm 𝒜] [IsStrictlyGradedComm ℬ]

/-- Transport of a divided power structure along an algebra equivalence matching the gradings:
the operations are conjugated, `δₙ y = e (γₙ (e⁻¹ y))`. -/
public noncomputable def DividedPowerStructure.transport (γ : DividedPowerStructure 𝒜)
    (e : A ≃ₐ[R] B) (he : ∀ (m : ℕ) (x : A), x ∈ 𝒜 m ↔ e x ∈ ℬ m) :
    DividedPowerStructure ℬ where
  dpow n y := e (γ.dpow n (e.symm y))
  dpow_null hy := by
    rw [γ.dpow_null fun h ↦ hy ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mpr h), map_zero]
  dpow_zero hy := by
    rw [γ.dpow_zero ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hy), map_one]
  dpow_one hy := by
    rw [γ.dpow_one ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hy), e.apply_symm_apply]
  dpow_mem hn hy := by
    refine (mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mpr ?_
    rw [e.symm_apply_apply]
    exact γ.dpow_mem hn ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hy)
  dpow_mem_grade hn hy hyg := by
    refine (he _ _).mp (γ.dpow_mem_grade hn
      ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hy) ?_)
    refine (he _ _).mpr ?_
    rwa [e.apply_symm_apply]
  dpow_mul hy := by
    rw [← map_mul, γ.dpow_mul ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hy), map_mul,
      map_natCast]
  dpow_mul_even hn hx hy := by
    rw [map_mul, γ.dpow_mul_even hn ((mem_evenPart_equiv_iff 𝒜 ℬ e he _).mp hx)
      ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hy), map_mul, map_pow,
      e.apply_symm_apply]
  dpow_mul_odd hn hx hy := by
    rw [map_mul, γ.dpow_mul_odd hn ((he _ _).mpr (by rwa [e.apply_symm_apply]))
      ((he _ _).mpr (by rwa [e.apply_symm_apply])), map_zero]
  dpow_add hx hy := by
    rw [map_add, γ.dpow_add ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hx)
      ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hy), map_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ map_mul _ _ _
  dpow_dpow hm hn hx := by
    rw [e.symm_apply_apply, γ.dpow_dpow hm hn
      ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he _).mp hx), map_mul, map_natCast]

/-- The divided powers of the transported structure are `δₙ y = e (γₙ (e⁻¹ y))`. -/
@[simp]
public theorem DividedPowerStructure.transport_dpow (γ : DividedPowerStructure 𝒜)
    (e : A ≃ₐ[R] B) (he : ∀ (m : ℕ) (x : A), x ∈ 𝒜 m ↔ e x ∈ ℬ m) (n : ℕ) (y : B) :
    (γ.transport e he).dpow n y = e (γ.dpow n (e.symm y)) := rfl

/-- Compatibility with a differential transports along an algebra equivalence matching the
gradings, provided the two differentials correspond. -/
public theorem IsCompatibleWithDifferential.transport (γ : DividedPowerStructure 𝒜)
    (e : A ≃ₐ[R] B) (he : ∀ (m : ℕ) (x : A), x ∈ 𝒜 m ↔ e x ∈ ℬ m)
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B) (hd : ∀ x : A, dB (e x) = e (dA x))
    (hc : IsCompatibleWithDifferential γ dA) :
    IsCompatibleWithDifferential (γ.transport e he) dB where
  d_dpow {n} {y} hn hy := by
    rw [DividedPowerStructure.transport_dpow, DividedPowerStructure.transport_dpow, hd,
      hc.d_dpow hn ((mem_positiveEvenPart_equiv_iff 𝒜 ℬ e he y).mp hy), map_mul, ← hd,
      e.apply_symm_apply]

end Transport

section DpowZero

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

/-- A positive divided power of zero is zero. -/
public theorem DividedPowerStructure.dpow_apply_zero (γ : DividedPowerStructure 𝒜) {n : ℕ}
    (hn : n ≠ 0) : γ.dpow n 0 = 0 := by
  have h := γ.dpow_mul_even (n := n) (x := 0) (y := 0) hn (Submodule.zero_mem _)
    (Submodule.zero_mem _)
  rw [mul_zero] at h
  rw [h, zero_pow hn, zero_mul]

end DpowZero

section Bot

open scoped Classical in
/-- A graded algebra whose positive even part vanishes carries a divided power structure: the
zeroth divided power of the zero element is one and every other value is zero. -/
public noncomputable def dividedPowerStructureOfPositiveEvenPartEqBot
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (h : positiveEvenPart 𝒜 = ⊥) : DividedPowerStructure 𝒜 where
  dpow n x := if n = 0 ∧ x = 0 then 1 else 0
  dpow_null {n x} hx := by
    have hx0 : x ≠ 0 := fun hq ↦ hx (hq ▸ Submodule.zero_mem _)
    simp [hx0]
  dpow_zero {x} hx := by
    obtain rfl : x = 0 := by rwa [h] at hx
    simp
  dpow_one {x} hx := by
    obtain rfl : x = 0 := by rwa [h] at hx
    simp
  dpow_mem {n x} hn _ := by
    rw [show (if n = 0 ∧ x = 0 then (1 : A) else 0) = 0 from by simp [hn]]
    exact Submodule.zero_mem _
  dpow_mem_grade {n d x} hn _ _ := by
    rw [show (if n = 0 ∧ x = 0 then (1 : A) else 0) = 0 from by simp [hn]]
    exact Submodule.zero_mem _
  dpow_mul {m n x} hx := by
    obtain rfl : x = 0 := by rwa [h] at hx
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rcases Nat.eq_zero_or_pos m with hm | hm
      · simp [hn, hm]
      · simp [hn, Nat.pos_iff_ne_zero.mp hm]
    · simp [Nat.pos_iff_ne_zero.mp hn]
  dpow_mul_even {n x y} hn _ hy := by
    obtain rfl : y = 0 := by rwa [h] at hy
    simp [hn]
  dpow_mul_odd {n d f x y} hn _ _ := by
    have hn' : n ≠ 0 := by omega
    simp [hn']
  dpow_add {n x y} hx hy := by
    obtain rfl : x = 0 := by rwa [h] at hx
    obtain rfl : y = 0 := by rwa [h] at hy
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
      have hzero : ∀ z : A, (if n = 0 ∧ z = 0 then (1 : A) else 0) = 0 := by
        intro z; simp [hn']
      rw [hzero]
      refine (Finset.sum_eq_zero ?_).symm
      intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      rcases Nat.eq_zero_or_pos ij.1 with h1 | h1
      · have h2 : ij.2 ≠ 0 := by omega
        simp [h2]
      · simp [Nat.pos_iff_ne_zero.mp h1]
  dpow_dpow {m n x} hm hn hx := by
    obtain rfl : x = 0 := by rwa [h] at hx
    simp [hm, hn]

end Bot

end DividedPowers.TateResolution

end
