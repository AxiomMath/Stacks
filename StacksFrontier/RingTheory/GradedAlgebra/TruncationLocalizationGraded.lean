module

public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalization

/-!
# The degree-zero localization of the truncation algebra is the sum of the twists

Let `A = ⨁_{d ≥ 0} A_d` be a graded ring, let `B = ⨁_{d ≥ 0} A_{≥ d}` be its truncation algebra
and let `f ∈ A_d` be homogeneous. Writing `g = ψ f ∈ B_d`, the degree-zero part `(B[1/g])₀` of the
localization of `B` at `g` is graded by `Stacks.Truncation.awayGrading`, whose degree-`m` piece is
carried isomorphically by the comparison map `Stacks.Truncation.awayToLocalization` onto the
degree-`m` part `(A[1/f])_m` of the localization of `A` at `f`. This grading is a decomposition:

  `(B[1/g])₀ = ⨁_{m ≥ 0} (A[1/f])_m`.

## Main results

* `Stacks.Truncation.isInternal_awayGrading`: the pieces of `(B[1/g])₀` form an internal direct
  sum, so `(B[1/g])₀ = ⨁_{m ≥ 0} (A[1/f])_m`.
* `Stacks.Truncation.gradedRingAwayGrading`: the resulting graded-ring structure on `(B[1/g])₀`.
* `Stacks.Truncation.awayGradingEquivAwayPiece`: the degree-`m` piece of `(B[1/g])₀` is
  `(A[1/f])_m`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open DirectSum

namespace Stacks.Truncation

universe u

section Graded

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {f : A}

/-- Two fractions `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` with the same numerator agree. -/
theorem awayElt_congr (hf : f ∈ 𝒜 d) (k : ℕ) {a b : A} (hab : a = b)
    (ha : a ∈ truncation 𝒜 (k * d)) (hb : b ∈ truncation 𝒜 (k * d)) :
    awayElt 𝒜 d hf k a ha = awayElt 𝒜 d hf k b hb := by
  subst hab
  rfl

/-- A fraction whose numerator is a finite sum is the sum of the corresponding fractions. -/
theorem awayElt_sum (hf : f ∈ 𝒜 d) (k : ℕ) (S : Finset ℕ) (c : ℕ → A)
    (hc : ∀ j, c j ∈ truncation 𝒜 (k * d)) (hs : (∑ j ∈ S, c j) ∈ truncation 𝒜 (k * d)) :
    awayElt 𝒜 d hf k (∑ j ∈ S, c j) hs = ∑ j ∈ S, awayElt 𝒜 d hf k (c j) (hc j) := by
  refine awayToLocalization_injective 𝒜 d hf ?_
  rw [awayToLocalization_awayElt 𝒜 d hf k _ hs, map_sum, ← awayFrac_sum f S k c]
  exact Finset.sum_congr rfl fun j _ => (awayToLocalization_awayElt 𝒜 d hf k (c j) (hc j)).symm

/-- Every element of `(B_{ψ f})₀` is a finite sum of homogeneous elements. -/
theorem exists_sum_eq_awayGrading (hf : f ∈ 𝒜 d)
    (y : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :
    ∃ (S : Finset ℕ) (z : ℕ → HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)),
      (∀ m, z m ∈ awayGrading 𝒜 d hf m) ∧ y = ∑ m ∈ S, z m := by
  classical
  obtain ⟨k, a, ha, rfl⟩ := awayElt_surjective 𝒜 d hf y
  have hc (j : ℕ) : GradedRing.proj 𝒜 j a ∈ truncation 𝒜 (k * d) := by
    rcases lt_or_ge j (k * d) with hj | hj
    · exact proj_eq_zero_of_mem_truncation 𝒜 hj ha ▸ zero_mem _
    · exact mem_truncation_of_mem 𝒜 hj (SetLike.coe_mem _)
  refine ⟨(DirectSum.decompose 𝒜 a).support.image fun j => j - k * d,
    fun m => awayElt 𝒜 d hf k (GradedRing.proj 𝒜 (m + k * d) a) (hc _),
    fun m => awayElt_mem_awayGrading 𝒜 d hf
      (show GradedRing.proj 𝒜 (m + k * d) a ∈ 𝒜 (m + k * d) from SetLike.coe_mem _), ?_⟩
  have hS : ∀ j ∈ (DirectSum.decompose 𝒜 a).support, k * d ≤ j := by
    intro j hj
    by_contra hlt
    refine DFinsupp.mem_support_iff.mp hj (ZeroMemClass.coe_eq_zero.mp ?_)
    rw [← GradedRing.proj_apply]
    exact proj_eq_zero_of_mem_truncation 𝒜 (not_le.mp hlt) ha
  have hinj : Set.InjOn (fun j => j - k * d) (DirectSum.decompose 𝒜 a).support := by
    intro x hx y hy hxy
    have h1 := hS x hx
    have h2 := hS y hy
    simp only at hxy
    omega
  rw [Finset.sum_image hinj]
  have hterm : ∀ j ∈ (DirectSum.decompose 𝒜 a).support,
      awayElt 𝒜 d hf k (GradedRing.proj 𝒜 (j - k * d + k * d) a) (hc _) =
        awayElt 𝒜 d hf k (GradedRing.proj 𝒜 j a) (hc j) := fun j hj =>
    awayElt_congr 𝒜 d hf k
      (congrArg (fun i => GradedRing.proj 𝒜 i a) (Nat.sub_add_cancel (hS j hj))) _ _
  have hsa : (∑ j ∈ (DirectSum.decompose 𝒜 a).support, GradedRing.proj 𝒜 j a) ∈
      truncation 𝒜 (k * d) := by
    simpa only [GradedRing.proj_apply, DirectSum.sum_support_decompose 𝒜 a] using ha
  rw [Finset.sum_congr rfl hterm, ← awayElt_sum 𝒜 d hf k _ _ hc hsa]
  refine awayElt_congr 𝒜 d hf k ?_ _ _
  simp only [GradedRing.proj_apply]
  exact (DirectSum.sum_support_decompose 𝒜 a).symm

/-- A finite family of homogeneous elements of `(B_{ψ f})₀` of distinct degrees summing to zero
vanishes. -/
theorem eq_zero_of_sum_awayGrading_eq_zero (hf : f ∈ 𝒜 d) {S : Finset ℕ}
    {z : ℕ → HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)}
    (hz : ∀ m, z m ∈ awayGrading 𝒜 d hf m) (hsum : ∑ m ∈ S, z m = 0) {m : ℕ} (hm : m ∈ S) :
    z m = 0 := by
  classical
  choose l b hb hzb using fun j =>
    (mem_awayPiece_iff 𝒜 d hf j _).mp ((mem_awayGrading_iff 𝒜 d hf j (z j)).mp (hz j))
  set K := S.sup l
  have hlK : ∀ j ∈ S, l j ≤ K := fun j hj => Finset.le_sup hj
  have hzN (N j : ℕ) (h : l j ≤ N) :
      awayToLocalization 𝒜 (z j) = awayFrac f N (f ^ (N - l j) * b j) := by
    rw [hzb j, awayFrac_shift f (l j) (N - l j) (b j), Nat.add_sub_cancel' h]
  have h0 : awayFrac f K (∑ j ∈ S, f ^ (K - l j) * b j) = 0 := by
    rw [← awayFrac_sum f S K, ← Finset.sum_congr rfl fun j hj => hzN K j (hlK j hj), ← map_sum,
      hsum, map_zero]
  obtain ⟨n, hn⟩ := (awayFrac_eq_zero_iff f K _).mp h0
  set L := K + n with hLdef
  have hlL : ∀ j ∈ S, l j ≤ L := fun j hj => (hlK j hj).trans (Nat.le_add_right _ _)
  have hsum0 : ∑ j ∈ S, f ^ (L - l j) * b j = 0 := by
    have hrw : ∑ j ∈ S, f ^ (L - l j) * b j = f ^ n * ∑ j ∈ S, f ^ (K - l j) * b j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have he : L - l j = n + (K - l j) := by
        have := hlK j hj
        omega
      rw [he, pow_add, mul_assoc]
    rw [hrw, hn]
  have hdeg : ∀ j ∈ S, f ^ (L - l j) * b j ∈ 𝒜 (j + L * d) := by
    intro j hj
    have h1 : f ^ (L - l j) * b j ∈ 𝒜 ((L - l j) * d + (j + l j * d)) := by
      simpa [smul_eq_mul] using
        SetLike.mul_mem_graded (SetLike.pow_mem_graded (L - l j) hf) (hb j)
    have h2 : (L - l j) * d + (j + l j * d) = j + L * d := by
      zify [hlL j hj]
      ring
    exact h2 ▸ h1
  have hb0 : f ^ (L - l m) * b m = 0 := by
    have hproj := congrArg (GradedRing.proj 𝒜 (m + L * d)) hsum0
    rwa [map_sum, map_zero, Finset.sum_eq_single_of_mem m hm
      (fun j hj hjm => proj_of_mem_ne 𝒜 (hdeg j hj) fun h => hjm (Nat.add_right_cancel h)),
      (GradedRing.proj_apply 𝒜 _ _).trans (DirectSum.decompose_of_mem_same 𝒜 (hdeg m hm))] at hproj
  refine awayToLocalization_injective 𝒜 d hf ?_
  rw [map_zero, hzN L m (hlL m hm), hb0, awayFrac_zero]

/-- `(B_{ψ f})₀ = ⨁_{m ≥ 0} (A_f)_m`: the degree-zero part of the localization of the
truncation algebra at `ψ f` is the internal direct sum of its homogeneous pieces, which the
comparison map identifies with the homogeneous parts of `A_f` in nonnegative degrees. -/
@[stacks 0EKG "the equality of homogeneous parts (B[1/ψ f])_0 = ⨁_{m ≥ 0} (A[1/f])_m, the \
ring-theoretic form of the identification of π_* O_L with the sum of the nonnegative twists"]
theorem isInternal_awayGrading (hf : f ∈ 𝒜 d) :
    DirectSum.IsInternal (awayGrading 𝒜 d hf) := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun y => ?_⟩
  · refine DFinsupp.ext fun m => ?_
    by_cases hm : m ∈ x.support
    · have hsum : ∑ j ∈ x.support,
          ((x j : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f))) = 0 := by
        rw [← hx, DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
        rfl
      exact ZeroMemClass.coe_eq_zero.mp
        (eq_zero_of_sum_awayGrading_eq_zero 𝒜 d hf (fun j => (x j).2) hsum hm)
    · exact DFinsupp.notMem_support_iff.mp hm
  · obtain ⟨S, z, hz, rfl⟩ := exists_sum_eq_awayGrading 𝒜 d hf y
    refine ⟨∑ m ∈ S, DirectSum.of (fun m : ℕ => ↥(awayGrading 𝒜 d hf m)) m ⟨z m, hz m⟩, ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => DirectSum.coeAddMonoidHom_of _ _ _

/-- The graded-ring structure on `(B_{ψ f})₀` given by the pieces
`Stacks.Truncation.awayGrading`. -/
@[instance_reducible]
def gradedRingAwayGrading (hf : f ∈ 𝒜 d) : GradedRing (awayGrading 𝒜 d hf) :=
  { instGradedMonoidAwayGrading 𝒜 d hf,
    (isInternal_awayGrading 𝒜 d hf).chooseDecomposition with }

/-- The comparison map on the degree-`m` piece of `(B_{ψ f})₀`, landing in `(A_f)_m`. -/
def awayGradingToAwayPiece (hf : f ∈ 𝒜 d) (m : ℕ) :
    awayGrading 𝒜 d hf m →+ awayPiece 𝒜 d hf m where
  toFun y := ⟨awayToLocalization 𝒜 (y : _), (mem_awayGrading_iff 𝒜 d hf m _).mp y.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' y y' := Subtype.ext (by simp)

/-- The degree-`m` piece of `(B_{ψ f})₀` is the degree-`m` part `(A_f)_m` of `A_f`. -/
@[stacks 0EKG "the degree-m piece of (B[1/ψ f])_0 is (A[1/f])_m"]
def awayGradingEquivAwayPiece (hf : f ∈ 𝒜 d) (m : ℕ) :
    awayGrading 𝒜 d hf m ≃+ awayPiece 𝒜 d hf m :=
  AddEquiv.ofBijective (awayGradingToAwayPiece 𝒜 d hf m)
    ⟨fun y y' h => Subtype.ext
        (awayToLocalization_injective 𝒜 d hf (congrArg Subtype.val h)),
      fun z => by
        obtain ⟨y, hy, hyz⟩ := exists_mem_awayGrading 𝒜 d hf m z.2
        exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩⟩

end Graded

end Stacks.Truncation

end
