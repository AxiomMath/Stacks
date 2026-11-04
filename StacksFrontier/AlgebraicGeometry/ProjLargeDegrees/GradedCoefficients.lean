module

public import Mathlib.Algebra.Module.GradedModule
public import StacksFrontier.Algebra.DirectSum.RangeGrading
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# Homogeneous coefficients in a graded module

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a graded ring and `W = ⨁_{n ∈ ℤ} ℳ n` a graded `A`-module. This file
proves two facts about the homogeneous decomposition.

* The degree-`(i + e)` component of `c · y`, for `y` homogeneous of degree `e` and `c` an
  arbitrary element of `A`, is the degree-`i` component of `c` acting on `y`. This is the module
  analogue of `DirectSum.coe_decompose_mul_add_of_right_mem`.
* A homogeneous element of degree `p` in the `A`-span of homogeneous elements `y j` of degrees
  `d j` is a combination `∑ a j · y j` with each `a j` homogeneous of the complementary degree.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.gradedProj`: the degree-`p` component of an element
  of a graded module, as an additive homomorphism back to the module.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.gradedProj_eq_self`,
  `Stacks.AlgebraicGeometry.ProjLargeDegrees.sum_support_gradedProj`,
  `Stacks.AlgebraicGeometry.ProjLargeDegrees.notMem_support_of_gradedProj_eq_zero`: the three
  basic facts about that homomorphism.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.gradedProj_rangeGrading`: for the tautological
  grading of a direct sum the component is the inclusion of the corresponding summand.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.coe_decompose_smul_of_left_mem`: for `a` homogeneous
  of degree `i`, the degree-`n` component of `a · y` is `a` times the degree-`n - i` component
  of `y`.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.coe_decompose_smul_add_of_right_mem`: for `y`
  homogeneous of degree `e`, the degree-`(i + e)` component of `c · y` is the degree-`i`
  component of `c` acting on `y`.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_homogeneous_smul_coeffs`: a homogeneous
  element of the span of homogeneous elements has homogeneous coefficients of the complementary
  degrees.

## References

* [Stacks Project, Tag 00JL](https://stacks.math.columbia.edu/tag/00JL)
-/

@[expose] public noncomputable section

open DirectSum
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegrees

universe u v w t

section Proj

variable {W : Type v} {τ : Type t} [AddCommGroup W]
  [SetLike τ W] [AddSubgroupClass τ W] (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]

/-- **The degree-`p` component of an element of a graded module**, as an additive homomorphism
back to the module. -/
def gradedProj (p : ℤ) : W →+ W where
  toFun z := ((DirectSum.decompose ℳ z p : ℳ p) : W)
  map_zero' := by simp
  map_add' z z' := by
    rw [DirectSum.decompose_add, DFinsupp.add_apply, AddMemClass.coe_add]

/-- `gradedProj ℳ p z` is the coercion to `W` of the degree-`p` component of the decomposition
of `z`. -/
@[simp]
theorem gradedProj_apply (p : ℤ) (z : W) :
    gradedProj ℳ p z = ((DirectSum.decompose ℳ z p : ℳ p) : W) := rfl

/-- **A homogeneous element is its own degree-`p` component.** -/
theorem gradedProj_eq_self {p : ℤ} {z : W} (hz : z ∈ ℳ p) : gradedProj ℳ p z = z := by
  rw [gradedProj_apply, DirectSum.decompose_of_mem_same ℳ hz]

/-- **The homogeneous components of an element sum to it.** -/
theorem sum_support_gradedProj [∀ (i : ℤ) (x : ℳ i), Decidable (x ≠ 0)] (z : W) :
    ∑ p ∈ (DirectSum.decompose ℳ z).support, gradedProj ℳ p z = z :=
  DirectSum.sum_support_decompose ℳ z

/-- **A degree whose component vanishes does not occur in the support.** -/
theorem notMem_support_of_gradedProj_eq_zero [∀ (i : ℤ) (x : ℳ i), Decidable (x ≠ 0)]
    {p : ℤ} {z : W} (h : gradedProj ℳ p z = 0) :
    p ∉ (DirectSum.decompose ℳ z).support :=
  fun hp => DFinsupp.mem_support_iff.mp hp (ZeroMemClass.coe_eq_zero.mp h)

/-- A homogeneous element of degree `j` has degree-`n` component itself if `n = j`, else zero. -/
private theorem gradedProj_of_mem {j : ℤ} {z : W} (hz : z ∈ ℳ j) (n : ℤ) :
    gradedProj ℳ n z = if n = j then z else 0 := by
  split_ifs with h
  · subst h
    exact gradedProj_eq_self ℳ hz
  · rw [gradedProj_apply, DirectSum.decompose_of_mem_ne ℳ hz (Ne.symm h)]

end Proj

/-! ### The tautological grading of a direct sum -/

/-- **For the tautological grading of a direct sum, the degree-`p` component of `z` is the
`p`-th summand of `z`, included back into the direct sum.** Here `ℳ` is any grading equal to
`DirectSum.rangeGrading ℤ V`, with its own `DirectSum.Decomposition` instance. -/
theorem gradedProj_rangeGrading {V : ℤ → Type v} [∀ i, AddCommGroup (V i)]
    (ℳ : ℤ → Submodule ℤ (DirectSum ℤ V)) [DirectSum.Decomposition ℳ]
    (hℳ : ℳ = DirectSum.rangeGrading ℤ V) (p : ℤ) (z : DirectSum ℤ V) :
    gradedProj ℳ p z = DirectSum.of V p (DirectSum.component ℤ ℤ V p z) := by
  classical
  subst hℳ
  induction z using DirectSum.induction_on with
  | zero => simp
  | of j a =>
      have hmem : DirectSum.of V j a ∈ DirectSum.rangeGrading ℤ V j :=
        (DirectSum.mem_rangeGrading ℤ V j _).mpr ⟨a, rfl⟩
      rw [gradedProj_of_mem _ hmem, ← DirectSum.apply_eq_component]
      split_ifs with hpj
      · subst hpj
        rw [DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ hpj, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

/-! ### Homogeneous coefficients -/

variable {A : Type u} {W : Type v} {σ : Type w} {τ : Type t}
  [CommRing A] [AddCommGroup W] [Module A W]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ W] [AddSubgroupClass τ W] (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **For `a` homogeneous of degree `i`, the degree-`n` component of `a · y` is `a` times the
degree-`n - i` component of `y`.** -/
theorem coe_decompose_smul_of_left_mem {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) (y : W) (n : ℤ) :
    gradedProj ℳ n (a • y) = a • gradedProj ℳ (n - (i : ℤ)) y := by
  classical
  induction y using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous y =>
      rename_i j
      have hay : a • (y : W) ∈ ℳ ((i : ℤ) + j) :=
        SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha y.2
      rw [gradedProj_of_mem ℳ hay, gradedProj_of_mem ℳ y.2]
      simp only [sub_eq_iff_eq_add']
      split_ifs <;> simp
  | add y y' hy hy' =>
      rw [smul_add, map_add, map_add, hy, hy', smul_add]

/-- For `y` homogeneous of degree `e` and `c` arbitrary, the degree-`(i + e)` component of `c · y`
is the degree-`i` component of `c` acting on `y`; the module analogue of
`DirectSum.coe_decompose_mul_add_of_right_mem`. -/
theorem coe_decompose_smul_add_of_right_mem {e : ℤ} {y : W} (hy : y ∈ ℳ e) (c : A) (i : ℕ) :
    gradedProj ℳ ((i : ℤ) + e) (c • y) = (DirectSum.decompose 𝒜 c i : A) • y := by
  classical
  induction c using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous c =>
      rename_i j
      rw [coe_decompose_smul_of_left_mem 𝒜 ℳ c.2 y ((i : ℤ) + e)]
      rw [gradedProj_of_mem ℳ hy]
      by_cases hij : j = i
      · subst hij
        rw [DirectSum.decompose_of_mem_same 𝒜 c.2]
        simp
      · rw [DirectSum.decompose_of_mem_ne 𝒜 c.2 hij]
        simp [sub_eq_iff_eq_add', Ne.symm hij]
  | add c c' hc hc' =>
      rw [add_smul, map_add, hc, hc', DirectSum.decompose_add, DFinsupp.add_apply,
        AddMemClass.coe_add, add_smul]

/-- **Homogeneous coefficients.** A homogeneous element of degree `p` of the `A`-span of
homogeneous elements `y j` of degrees `d j` is a combination `∑ a j · y j` with each `a j`
homogeneous of the complementary degree `e j`, where `e j + d j = p`. -/
theorem exists_homogeneous_smul_coeffs {r : ℕ} (y : Fin r → W) (d : Fin r → ℤ) (e : Fin r → ℕ)
    (hy : ∀ j, y j ∈ ℳ (d j)) {p : ℤ} (he : ∀ j, (e j : ℤ) + d j = p) {z : W} (hz : z ∈ ℳ p)
    (hmem : z ∈ Submodule.span A (Set.range y)) :
    ∃ a : (j : Fin r) → 𝒜 (e j), z = ∑ j, (a j : A) • y j := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hmem
  refine ⟨fun j => DirectSum.decompose 𝒜 (c j) (e j), ?_⟩
  calc z = gradedProj ℳ p z := (gradedProj_eq_self ℳ hz).symm
    _ = ∑ j, gradedProj ℳ p (c j • y j) := by rw [← hc, map_sum]
    _ = ∑ j, (DirectSum.decompose 𝒜 (c j) (e j) : A) • y j := Finset.sum_congr rfl fun j _ => by
        rw [← he j, coe_decompose_smul_add_of_right_mem 𝒜 ℳ (hy j) (c j) (e j)]

end Stacks.AlgebraicGeometry.ProjLargeDegrees

end
