module

public import StacksFrontier.Algebra.DGA.Abelian
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology

/-!
# A nonnegatively graded differential graded algebra, read cohomologically

A differential graded algebra in the sense of divided-power algebra is graded by `ℕ` and its
differential lowers degrees by one. Chapter 22's bundled `DifferentialGradedAlgebra` is graded
by `ℤ` and its differential raises degrees by one. Reading the homological degree `k` in
cohomological degree `-k` converts the first into the second: the underlying algebra, its
multiplication and its differential are unchanged, and only the index set is renamed.

## Main definitions

* `DividedPowers.TateResolution.cohomologicalGrade`: a nonnegative grading read cohomologically,
  with the homological degree `k` in degree `-k` and nothing in positive degrees.
* `DividedPowers.TateResolution.regradedDifferentialGradedAlgebra`: a nonnegatively graded
  algebra with a differential satisfying `IsDifferentialGradedAlgebra`, as an object of
  `DifferentialGradedAlgebra`.

## Main results

* `DividedPowers.TateResolution.cohomologicalGrade_neg_natCast`: degree `-k` is the homogeneous
  piece of homological degree `k`.
* `DividedPowers.TateResolution.cohomologicalGrade.gradedAlgebra`: the regraded pieces still
  decompose the algebra.

## Implementation notes

`DifferentialGradedAlgebra` bundles its grading as a `GradedAlgebra`, hence as a genuine
`DirectSum.Decomposition` indexed by `ℤ`, so the `ℕ`-indexed decomposition has to be transported
along `k ↦ -k`. The additive map `toCohomologicalGradeDirectSum` reindexes the direct sum
summandwise, using `LinearEquiv.ofEq` to identify the piece of homological degree `k` with the
piece of cohomological degree `-k`, and the two round-trip identities are checked on the
summands with `DirectSum.addHom_ext`. The sign in the Leibniz rule is unchanged by the
regrading, because `(-1) ^ (-k) = (-1) ^ k`.

## References

* [Stacks Project, Tag 061V](https://stacks.math.columbia.edu/tag/061V)
* [Stacks Project, Tag 09PJ](https://stacks.math.columbia.edu/tag/09PJ)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

open scoped DirectSum

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

section Grading

variable (𝒜 : ℕ → Submodule R A)

/-- A nonnegative grading read cohomologically: the piece of homological degree `k` sits in
degree `-k`, and there is nothing in positive degrees. -/
def cohomologicalGrade (n : ℤ) : Submodule R A :=
  if n ≤ 0 then 𝒜 (-n).toNat else ⊥

/-- In a nonpositive degree `n` the cohomological piece is the homological piece of degree
`-n`. -/
theorem cohomologicalGrade_of_nonpos {n : ℤ} (hn : n ≤ 0) :
    cohomologicalGrade 𝒜 n = 𝒜 (-n).toNat := by
  simp [cohomologicalGrade, hn]

/-- The cohomological pieces in positive degrees vanish. -/
theorem cohomologicalGrade_of_pos {n : ℤ} (hn : 0 < n) : cohomologicalGrade 𝒜 n = ⊥ := by
  simp [cohomologicalGrade, show ¬ n ≤ 0 from by omega]

/-- The piece of cohomological degree `-k` is the piece of homological degree `k`. -/
@[simp]
theorem cohomologicalGrade_neg_natCast (k : ℕ) :
    cohomologicalGrade 𝒜 (-(k : ℤ)) = 𝒜 k := by
  rw [cohomologicalGrade_of_nonpos 𝒜 (by omega)]
  congr 1
  omega

/-- The cohomological piece of degree `0` is the homological piece of degree `0`. -/
theorem cohomologicalGrade_zero : cohomologicalGrade 𝒜 0 = 𝒜 0 := by
  simpa using cohomologicalGrade_neg_natCast 𝒜 0

/-- An element of a cohomological piece of positive degree is zero. -/
theorem eq_zero_of_mem_cohomologicalGrade_of_pos {n : ℤ} (hn : 0 < n) {x : A}
    (hx : x ∈ cohomologicalGrade 𝒜 n) : x = 0 := by
  rw [cohomologicalGrade_of_pos 𝒜 hn] at hx
  simpa using hx

/-- The cohomological pieces of a graded monoid again form a graded monoid: degrees add
under `k ↦ -k`, and a product with a factor of positive degree is zero. -/
instance cohomologicalGrade.gradedMonoid [SetLike.GradedMonoid 𝒜] :
    SetLike.GradedMonoid (cohomologicalGrade 𝒜) where
  one_mem := by
    rw [cohomologicalGrade_zero]
    exact SetLike.one_mem_graded 𝒜
  mul_mem := by
    intro i j a b ha hb
    by_cases hi : i ≤ 0
    · by_cases hj : j ≤ 0
      · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
        rw [cohomologicalGrade_neg_natCast] at ha hb
        rw [show -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ) by push_cast; ring,
          cohomologicalGrade_neg_natCast]
        exact SetLike.mul_mem_graded ha hb
      · rw [eq_zero_of_mem_cohomologicalGrade_of_pos 𝒜 (by omega) hb, mul_zero]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_mem_cohomologicalGrade_of_pos 𝒜 (by omega) ha, zero_mul]
      exact Submodule.zero_mem _

/-- The piece of homological degree `k`, read as the piece of cohomological degree `-k`. -/
def gradeToCohomologicalGrade (k : ℕ) : 𝒜 k ≃ₗ[R] cohomologicalGrade 𝒜 (-(k : ℤ)) :=
  LinearEquiv.ofEq _ _ (cohomologicalGrade_neg_natCast 𝒜 k).symm

/-- Reading a homological piece cohomologically does not change the underlying element. -/
@[simp]
theorem coe_gradeToCohomologicalGrade (k : ℕ) (x : 𝒜 k) :
    (gradeToCohomologicalGrade 𝒜 k x : A) = x := rfl

/-- The reindexing `k ↦ -k` of a direct sum of homological pieces as a direct sum of
cohomological pieces. -/
def toCohomologicalGradeDirectSum :
    (⨁ k : ℕ, 𝒜 k) →+ ⨁ n : ℤ, cohomologicalGrade 𝒜 n :=
  DirectSum.toAddMonoid fun k =>
    (DirectSum.of _ (-(k : ℤ))).comp
      (gradeToCohomologicalGrade 𝒜 k).toLinearMap.toAddMonoidHom

/-- The reindexing `toCohomologicalGradeDirectSum` sends the summand of homological degree `k`
to the summand of cohomological degree `-k`. -/
@[simp]
theorem toCohomologicalGradeDirectSum_of (k : ℕ) (x : 𝒜 k) :
    toCohomologicalGradeDirectSum 𝒜 (DirectSum.of _ k x) =
      DirectSum.of _ (-(k : ℤ)) (gradeToCohomologicalGrade 𝒜 k x) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The reindexing `toCohomologicalGradeDirectSum` does not change the sum in `A` of the
components. -/
theorem coe_toCohomologicalGradeDirectSum (x : ⨁ k : ℕ, 𝒜 k) :
    DirectSum.coeAddMonoidHom (cohomologicalGrade 𝒜) (toCohomologicalGradeDirectSum 𝒜 x) =
      DirectSum.coeAddMonoidHom 𝒜 x := by
  have h : (DirectSum.coeAddMonoidHom (cohomologicalGrade 𝒜)).comp
      (toCohomologicalGradeDirectSum 𝒜) = DirectSum.coeAddMonoidHom 𝒜 :=
    DirectSum.addHom_ext fun k y => by simp
  exact DFunLike.congr_fun h x

/-- The decomposition of the algebra into its cohomological pieces: decompose into homological
pieces, then reindex by `k ↦ -k`. -/
noncomputable def cohomologicalGradeDecompose [GradedRing 𝒜] :
    A →+ ⨁ n : ℤ, cohomologicalGrade 𝒜 n :=
  (toCohomologicalGradeDirectSum 𝒜).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

/-- `cohomologicalGradeDecompose` is the homological decomposition followed by the reindexing
`toCohomologicalGradeDirectSum`. -/
theorem cohomologicalGradeDecompose_apply [GradedRing 𝒜] (a : A) :
    cohomologicalGradeDecompose 𝒜 a = toCohomologicalGradeDirectSum 𝒜 (DirectSum.decompose 𝒜 a) :=
  rfl

/-- Summing the components of the cohomological decomposition of `a` recovers `a`. -/
theorem coe_cohomologicalGradeDecompose [GradedRing 𝒜] (a : A) :
    DirectSum.coeAddMonoidHom (cohomologicalGrade 𝒜) (cohomologicalGradeDecompose 𝒜 a) = a := by
  rw [cohomologicalGradeDecompose_apply, coe_toCohomologicalGradeDirectSum]
  exact (DirectSum.decompose 𝒜).symm_apply_apply a

/-- Decomposing the sum of a family of cohomological components recovers the family. -/
theorem cohomologicalGradeDecompose_coe [GradedRing 𝒜] (y : ⨁ n : ℤ, cohomologicalGrade 𝒜 n) :
    cohomologicalGradeDecompose 𝒜
        (DirectSum.coeAddMonoidHom (cohomologicalGrade 𝒜) y) = y := by
  have h : (cohomologicalGradeDecompose 𝒜).comp
      (DirectSum.coeAddMonoidHom (cohomologicalGrade 𝒜)) = AddMonoidHom.id _ := by
    refine DirectSum.addHom_ext fun n x => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply]
    by_cases hn : n ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
      have hx : (x : A) ∈ 𝒜 k := by
        rw [← cohomologicalGrade_neg_natCast 𝒜 k]
        exact x.2
      have hdec : DirectSum.decompose 𝒜 (x : A) =
          DirectSum.of _ k (⟨(x : A), hx⟩ : 𝒜 k) :=
        DirectSum.decompose_coe 𝒜 (⟨(x : A), hx⟩ : 𝒜 k)
      rw [cohomologicalGradeDecompose_apply, hdec, toCohomologicalGradeDirectSum_of]
      exact congrArg (fun z => DirectSum.of _ (-(k : ℤ)) z) (Subtype.ext rfl)
    · have hx0 : x = 0 :=
        Subtype.ext (eq_zero_of_mem_cohomologicalGrade_of_pos 𝒜 (by omega) x.2)
      rw [hx0]
      simp
  exact DFunLike.congr_fun h y

/-- The cohomological pieces of a graded ring decompose it, by
`cohomologicalGradeDecompose`. -/
noncomputable instance cohomologicalGrade.decomposition [GradedRing 𝒜] :
    DirectSum.Decomposition (cohomologicalGrade 𝒜) where
  decompose' := cohomologicalGradeDecompose 𝒜
  left_inv := coe_cohomologicalGradeDecompose 𝒜
  right_inv := cohomologicalGradeDecompose_coe 𝒜

/-- The cohomological pieces of a graded algebra form a graded algebra. -/
noncomputable instance cohomologicalGrade.gradedAlgebra [GradedAlgebra 𝒜] :
    GradedAlgebra (cohomologicalGrade 𝒜) :=
  { cohomologicalGrade.gradedMonoid 𝒜, cohomologicalGrade.decomposition 𝒜 with }

end Grading

section Differential

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 d]

/-- A differential lowering the homological degree by one raises the cohomological degree
by one. -/
theorem d_mem_cohomologicalGrade {n : ℤ} {a : A} (ha : a ∈ cohomologicalGrade 𝒜 n) :
    d a ∈ cohomologicalGrade 𝒜 (n + 1) := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
    rw [cohomologicalGrade_neg_natCast] at ha
    cases k with
    | zero =>
      rw [show -((0 : ℕ) : ℤ) + 1 = 1 by norm_num, cohomologicalGrade_of_pos 𝒜 (by omega),
        IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) ha]
      exact Submodule.zero_mem _
    | succ j =>
      rw [show -((j + 1 : ℕ) : ℤ) + 1 = -(j : ℤ) by push_cast; ring,
        cohomologicalGrade_neg_natCast]
      exact IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d) ha
  · rw [eq_zero_of_mem_cohomologicalGrade_of_pos 𝒜 (by omega) ha, map_zero]
    exact Submodule.zero_mem _

/-- The signed Leibniz rule read in the cohomological grading. The sign is unchanged by the
regrading, since `(-1) ^ (-k) = (-1) ^ k`. -/
theorem d_mul_of_mem_cohomologicalGrade {n m : ℤ} {a b : A}
    (ha : a ∈ cohomologicalGrade 𝒜 n) (hb : b ∈ cohomologicalGrade 𝒜 m) :
    d (a * b) = d a * b + (n.negOnePow : ℤ) • (a * d b) := by
  by_cases hn : n ≤ 0
  · by_cases hm : m ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
      obtain ⟨l, rfl⟩ := Int.exists_eq_neg_ofNat hm
      rw [cohomologicalGrade_neg_natCast] at ha hb
      have hcast : (((-1 : ℤ) ^ k : ℤ) : R) = (-1 : R) ^ k := by push_cast; ring
      rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d) ha hb, Int.negOnePow_neg,
        Int.coe_negOnePow_natCast, ← Int.cast_smul_eq_zsmul R, hcast]
    · rw [eq_zero_of_mem_cohomologicalGrade_of_pos 𝒜 (by omega) hb]
      simp
  · rw [eq_zero_of_mem_cohomologicalGrade_of_pos 𝒜 (by omega) ha]
    simp

/-- A nonnegatively graded algebra whose differential lowers degrees by one, read as an object
of `DifferentialGradedAlgebra`: the piece of homological degree `k` sits in cohomological
degree `-k`, and the algebra and its differential are unchanged. -/
noncomputable def regradedDifferentialGradedAlgebra : DifferentialGradedAlgebra.{u, v} R where
  A := A
  grading := cohomologicalGrade 𝒜
  d := d
  d_comp_d := LinearMap.ext fun x => IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := d) x
  d_mem := fun _ _ ha => d_mem_cohomologicalGrade 𝒜 d ha
  leibniz := fun _ _ _ _ ha hb => d_mul_of_mem_cohomologicalGrade 𝒜 d ha hb

/-- The grading of `regradedDifferentialGradedAlgebra` is the cohomological grading. -/
@[simp]
theorem regradedDifferentialGradedAlgebra_grading :
    (regradedDifferentialGradedAlgebra 𝒜 d).grading = cohomologicalGrade 𝒜 := rfl

/-- The differential of `regradedDifferentialGradedAlgebra` is the original differential. -/
@[simp]
theorem regradedDifferentialGradedAlgebra_d : (regradedDifferentialGradedAlgebra 𝒜 d).d = d := rfl

end Differential

end DividedPowers.TateResolution
