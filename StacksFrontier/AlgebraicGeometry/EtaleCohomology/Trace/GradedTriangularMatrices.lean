module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Matrix.Mul

/-!
# Graded upper triangular matrices

Let `d : ι → ℤ` grade the index set of square matrices.  A matrix `T` is *graded upper
triangular* when `T i j = 0` as soon as `d j < d i`, and its *graded diagonal part* keeps the
entries with `d i = d j`.  In a basis adapted to a flag `0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ V_s` of
subrepresentations (grade of a basis vector: the first `V_t` containing it), a representation is
graded upper triangular and its graded diagonal part is the semisimplification
`⊕ V_t / V_{t - 1}`.

Graded upper triangular matrices are closed under products and Kronecker products (with the sum
grading), and the graded diagonal part is multiplicative on them and commutes with Kronecker
products.  A common left eigenvector of a family of graded upper triangular matrices gives, by
keeping its components of lowest grade, a common left eigenvector of their graded diagonal parts
with the same eigenvalues.

## Main definitions

* `Stacks.EtaleCohomology.IsGradedUpper`, `Stacks.EtaleCohomology.gradedDiag`.

## Main results

* `Stacks.EtaleCohomology.IsGradedUpper.mul`, `Stacks.EtaleCohomology.gradedDiag_mul`.
* `Stacks.EtaleCohomology.IsGradedUpper.kronecker`, `Stacks.EtaleCohomology.gradedDiag_kronecker`.
* `Stacks.EtaleCohomology.exists_vecMul_gradedDiag_eq`: the lowest-grade part of a left
  eigenvector.
-/

@[expose] public noncomputable section

open Matrix
open scoped Kronecker

namespace Stacks.EtaleCohomology

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]

/-- A matrix is **graded upper triangular** for `d : ι → ℤ` when its `(i, j)` entry vanishes
whenever `d j < d i`. -/
public def IsGradedUpper (d : ι → ℤ) (T : Matrix ι ι R) : Prop :=
  ∀ i j, d j < d i → T i j = 0

/-- The **graded diagonal part**: the entries `(i, j)` with `d i = d j`. -/
public def gradedDiag (d : ι → ℤ) (T : Matrix ι ι R) : Matrix ι ι R :=
  fun i j => if d i = d j then T i j else 0

variable {d : ι → ℤ}

omit [Fintype ι] in
/-- The identity matrix is graded upper triangular. -/
public theorem isGradedUpper_one [DecidableEq ι] : IsGradedUpper d (1 : Matrix ι ι R) :=
  fun i _ h => Matrix.one_apply_ne (fun hij => (lt_irrefl (d i)) (hij ▸ h))

/-- A product of graded upper triangular matrices is graded upper triangular. -/
public theorem IsGradedUpper.mul {S T : Matrix ι ι R} (hS : IsGradedUpper d S)
    (hT : IsGradedUpper d T) : IsGradedUpper d (S * T) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (d k) (d i) with h | h
  · rw [hS i k h, zero_mul]
  · rw [hT k j (lt_of_lt_of_le hij h), mul_zero]

/-- A product vanishes when one factor vanishes on each side of the comparison `a ≠ b`. -/
private theorem mul_eq_zero_of_ne_of_lt {x y : R} {a b : ℤ} (hx : b < a → x = 0)
    (hy : a < b → y = 0) (hne : a ≠ b) : x * y = 0 := by
  obtain h | h := lt_or_gt_of_ne hne <;> simp [hx, hy, h]

omit [Fintype ι] in
/-- The graded diagonal part of the identity matrix is the identity matrix. -/
public theorem gradedDiag_one [DecidableEq ι] : gradedDiag d (1 : Matrix ι ι R) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [gradedDiag]
  · simp only [gradedDiag, Matrix.one_apply_ne hij, ite_self]

/-- **The graded diagonal part is multiplicative** on graded upper triangular matrices. -/
public theorem gradedDiag_mul {S T : Matrix ι ι R} (hS : IsGradedUpper d S)
    (hT : IsGradedUpper d T) : gradedDiag d (S * T) = gradedDiag d S * gradedDiag d T := by
  ext i j
  simp only [gradedDiag, Matrix.mul_apply]
  split_ifs with hij
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hik : d i = d k
    · rw [ite_eq_left hik, ite_eq_left (hik.symm.trans hij)]
    · rw [ite_eq_right hik, zero_mul]
      exact mul_eq_zero_of_ne_of_lt (hS i k) (fun h => hT k j (hij ▸ h)) hik
  · refine (Finset.sum_eq_zero fun k _ => ?_).symm
    split_ifs <;> simp_all

omit [Fintype ι] [Fintype κ] in
/-- Kronecker products of graded upper triangular matrices are graded upper triangular for the
sum grading. -/
public theorem IsGradedUpper.kronecker {d' : κ → ℤ} {S : Matrix ι ι R} {T : Matrix κ κ R}
    (hS : IsGradedUpper d S) (hT : IsGradedUpper d' T) :
    IsGradedUpper (fun p : ι × κ => d p.1 + d' p.2) (S ⊗ₖ T) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  rw [kronecker_apply]
  rcases lt_or_ge (d j) (d i) with h1 | h1
  · rw [hS i j h1, zero_mul]
  · have h2 : d' l < d' k := by simp only at h; omega
    rw [hT k l h2, mul_zero]

omit [Fintype ι] [Fintype κ] in
/-- **The graded diagonal part commutes with Kronecker products** of graded upper triangular
matrices. -/
public theorem gradedDiag_kronecker {d' : κ → ℤ} {S : Matrix ι ι R} {T : Matrix κ κ R}
    (hS : IsGradedUpper d S) (hT : IsGradedUpper d' T) :
    gradedDiag (fun p : ι × κ => d p.1 + d' p.2) (S ⊗ₖ T) =
      gradedDiag d S ⊗ₖ gradedDiag d' T := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [gradedDiag, kronecker_apply]
  by_cases h1 : d i = d j
  · by_cases h2 : d' k = d' l
    · rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_left h2]
    · rw [ite_eq_right (by omega), ite_eq_right h2, mul_zero]
  · rw [ite_eq_right h1, zero_mul]
    split_ifs with h
    · exact mul_eq_zero_of_ne_of_lt (hS i j) (fun _ => hT k l (by omega)) h1
    · rfl

/-- **The lowest-grade part of a common left eigenvector.**  Let `v ≠ 0` be a left eigenvector
of every matrix of a family of graded upper triangular matrices `T a`, with eigenvalues `c a`.
Then there is a nonzero `w` (the components of `v` of lowest grade) which is a left eigenvector
of every graded diagonal part `gradedDiag d (T a)`, with the same eigenvalue `c a`. -/
public theorem exists_vecMul_gradedDiag_eq {A : Type*} {T : A → Matrix ι ι R}
    (hT : ∀ a, IsGradedUpper d (T a)) {c : A → R} {v : ι → R} (hv : v ≠ 0)
    (hvT : ∀ a, v ᵥ* T a = c a • v) :
    ∃ w : ι → R, w ≠ 0 ∧ ∀ a, w ᵥ* gradedDiag d (T a) = c a • w := by
  classical
  have hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hv (funext fun i => by simpa using h (Finset.mem_univ i))
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ d hne
  set p := d i₀
  have hlow : ∀ i, d i < p → v i = 0 := fun i hi => by
    by_contra h
    exact absurd (hmin i (by simpa using h)) (not_le.mpr hi)
  refine ⟨fun i => if d i = p then v i else 0, ?_, fun a => ?_⟩
  · intro h
    have := congrFun h i₀
    rw [ite_eq_left rfl, Pi.zero_apply] at this
    exact (Finset.mem_filter.mp hi₀).2 this
  · ext j
    have hj := congrFun (hvT a) j
    simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hj ⊢
    by_cases hjp : d j = p
    · rw [ite_eq_left hjp, ← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [gradedDiag]
      by_cases hip : d i = p
      · rw [ite_eq_left hip, ite_eq_left (hip.trans hjp.symm)]
      · rw [ite_eq_right hip, zero_mul]
        exact (mul_eq_zero_of_ne_of_lt (hlow i) (fun _ => hT a i j (by omega)) (Ne.symm hip)).symm
    · rw [ite_eq_right hjp, mul_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [gradedDiag]
      by_cases hip : d i = p
      · rw [ite_eq_left hip, ite_eq_right (fun h => hjp (h.symm.trans hip)), mul_zero]
      · rw [ite_eq_right hip, zero_mul]

end Stacks.EtaleCohomology

end
