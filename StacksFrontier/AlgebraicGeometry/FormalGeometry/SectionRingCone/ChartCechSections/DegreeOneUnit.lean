module

public import StacksFrontier.RingTheory.HomogeneousLocalization.GradedLocalizedModule
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist

/-!
# A degree-one factor of the denominator makes the degree-one piece free of rank one

Let `S = ⨁_{i ≥ 0} 𝒜 i` be a graded ring, regarded as a `ℤ`-graded module over itself by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading`. Let `a ∈ 𝒜 d` be homogeneous and
suppose `a = t c` with `t ∈ 𝒜 1` and `c ∈ 𝒜 k`, `1 + k = d`. Then `t` is a unit of degree one in
`S_a` (its inverse is `c / a`), so multiplication by `t / 1` identifies the degree-zero
localization `S_(a)` with the degree-one part of `S_a`, and more generally multiplication by
`(t / 1) ^ j` shifts degrees by `j`.

This is the algebra behind the statement that the section `t` trivializes `L` on the chart `X_a`,
and it is what lets the ideal of a zero scheme be read inside the localization.

## Main results

* `Stacks.Algebraization.SectionRingCone.bijective_smul_mk_degreeOne` — `w ↦ w • (t / 1)` from
  `S_(a)` to the degree-one part of `S_a` is bijective.
* `Stacks.Algebraization.SectionRingCone.mk_mul_mem_gradedPiece_of_mem` — the arithmetic of
  degrees of fractions used throughout.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading integerGrading_natCast
  mem_homogeneousSubmodule)

attribute [local instance] instVAddNatIntGradedLocalizedModule

universe u w

namespace Stacks.Algebraization.SectionRingCone

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 (integerGrading (S := S) 𝒜)]

omit [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 (integerGrading (S := S) 𝒜)] in
/-- Membership in the natural-number degrees of the integer grading of `S`. -/
theorem mem_integerGrading_natCast_iff {i : ℕ} {x : S} :
    x ∈ integerGrading (S := S) 𝒜 (i : ℤ) ↔ x ∈ 𝒜 i := by
  rw [integerGrading_natCast, mem_homogeneousSubmodule]

omit [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 (integerGrading (S := S) 𝒜)] in
/-- A fraction `x / a ^ n` lies in degree `e` of `S_a` as soon as `x ∈ 𝒜 i` with
`i = e + n d`. -/
theorem mk_mem_gradedPiece_of_mem {d : ℕ} {a : S} (ha : a ∈ 𝒜 d) {e : ℤ} {n i : ℕ}
    (hi : (i : ℤ) = e + n • (d : ℤ)) {x : S} (hx : x ∈ 𝒜 i) :
    LocalizedModule.mk x (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) ∈
      Stacks.GradedLocalization.gradedPiece 𝒜 (integerGrading (S := S) 𝒜) a e := by
  refine Stacks.GradedLocalization.mk_mem_gradedPiece 𝒜 (integerGrading (S := S) 𝒜) ha ?_
  rw [← hi]
  exact (mem_integerGrading_natCast_iff 𝒜).2 hx

/-- An element of degree `e ≥ 0` of `S_a` is a fraction `x / a ^ n` with `x ∈ 𝒜 i`,
`i = e + n d`. -/
theorem exists_mk_of_mem_gradedPiece {d : ℕ} {a : S} (ha : a ∈ 𝒜 d) {e : ℤ} (he : 0 ≤ e)
    {z : LocalizedModule.Away (R := S) a S}
    (hz : z ∈ Stacks.GradedLocalization.gradedPiece 𝒜 (integerGrading (S := S) 𝒜) a e) :
    ∃ (n i : ℕ) (x : S), (i : ℤ) = e + n • (d : ℤ) ∧ x ∈ 𝒜 i ∧
      z = LocalizedModule.mk x (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) := by
  obtain ⟨n, x, hx, rfl⟩ :=
    (Stacks.GradedLocalization.mem_gradedPiece_iff 𝒜 (integerGrading (S := S) 𝒜) ha e z).1 hz
  have h0 : 0 ≤ e + n • (d : ℤ) := by
    have : (0 : ℤ) ≤ n • (d : ℤ) := by rw [nsmul_eq_mul]; positivity
    omega
  refine ⟨n, (e + n • (d : ℤ)).toNat, x, Int.toNat_of_nonneg h0, ?_, rfl⟩
  rw [← mem_integerGrading_natCast_iff, Int.toNat_of_nonneg h0]
  exact hx

variable {𝒜}

/-- **Multiplication by a degree-one factor of the denominator.** For `a = t c` with `t ∈ 𝒜 1`
and `c ∈ 𝒜 k`, `1 + k = d`, the map `w ↦ w • (t / 1)` from the degree-zero localization `S_(a)`
to the degree-one part of `S_a` is a bijection onto that part. -/
theorem bijective_smul_mk_degreeOne {d k : ℕ} {a t c : S} (ha : a ∈ 𝒜 d) (ht : t ∈ 𝒜 1)
    (hc : c ∈ 𝒜 k) (hk : 1 + k = d) (hac : t * c = a) :
    (∀ w : HomogeneousLocalization.Away 𝒜 a,
      w.val • LocalizedModule.mk t (1 : Submonoid.powers a) ∈
        Stacks.GradedLocalization.gradedPiece 𝒜 (integerGrading (S := S) 𝒜) a 1) ∧
    Function.Injective (fun w : HomogeneousLocalization.Away 𝒜 a =>
      w.val • LocalizedModule.mk t (1 : Submonoid.powers a)) ∧
    ∀ z ∈ Stacks.GradedLocalization.gradedPiece 𝒜 (integerGrading (S := S) 𝒜) a 1,
      ∃ w : HomogeneousLocalization.Away 𝒜 a,
        w.val • LocalizedModule.mk t (1 : Submonoid.powers a) = z := by
  refine ⟨fun w => ?_, fun w w' hww' => ?_, fun z hz => ?_⟩
  · obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha w
    rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
    have hx' : x • t ∈ 𝒜 (n • d + 1) := by
      rw [smul_eq_mul]; exact SetLike.mul_mem_graded hx ht
    have h1 : (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) * 1 = ⟨a ^ n, n, rfl⟩ := mul_one _
    rw [h1]
    exact mk_mem_gradedPiece_of_mem 𝒜 ha
      (by simp only [smul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]; ring) hx'
  · -- multiply by `c / a`, the inverse of `t`
    have key : ∀ w : HomogeneousLocalization.Away 𝒜 a,
        (Localization.mk c (⟨a, 1, pow_one a⟩ : Submonoid.powers a)) •
          (w.val • LocalizedModule.mk t (1 : Submonoid.powers a)) =
          w.val • LocalizedModule.mk (1 : S) (1 : Submonoid.powers a) := by
      intro w
      rw [smul_comm, LocalizedModule.mk_smul_mk]
      congr 1
      rw [LocalizedModule.mk_eq]
      exact ⟨1, by simp [Submonoid.smul_def, ← hac, mul_comm]⟩
    have h := congrArg (fun z => (Localization.mk c (⟨a, 1, pow_one a⟩ : Submonoid.powers a)) •
      z) hww'
    simp only at h
    rw [key, key] at h
    apply HomogeneousLocalization.val_injective
    obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha w
    obtain ⟨n', x', hx', rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha w'
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk] at h ⊢
    rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨u, ?_⟩
    simp only [Submonoid.smul_def, smul_eq_mul, mul_one] at hu
    linear_combination hu
  · obtain ⟨n, i, x, hi, hx, rfl⟩ := exists_mk_of_mem_gradedPiece 𝒜 ha zero_le_one hz
    have hxc : x * c ∈ 𝒜 ((n + 1) • d) := by
      have hdeg : (n + 1) • d = i + k := by
        have hi' : i = 1 + n * d := by
          have : (i : ℤ) = 1 + (n : ℤ) * d := by simpa using hi
          exact_mod_cast this
        rw [smul_eq_mul, hi', ← hk]; ring
      rw [hdeg]; exact SetLike.mul_mem_graded hx hc
    refine ⟨HomogeneousLocalization.Away.mk 𝒜 ha (n + 1) (x * c) hxc, ?_⟩
    rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
    refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_eq_mul, mul_one]
    rw [← hac]; ring

end Stacks.Algebraization.SectionRingCone

end
