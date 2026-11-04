module

public import Mathlib.Data.Matrix.Basis
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorHomGroups

/-!
# Elements of the upper triangular algebra of `ℙ¹_ℤ`

`Stacks.AlgebraicGeometry.ProjectiveGenerator.endomorphismMatrices` is the algebra `R` of
[Stacks, Tag 0CS9]: the `(n + 1) × (n + 1)` matrices over `S = A[X₀, …, Xₙ]` whose `(i, j)` entry
is homogeneous of degree `j - i`. For `A = ℤ` and `n = 1` this file exhibits an element of `R`
that is not a scalar, shows that the homogeneity condition excludes some matrices and that its
degree is sharp, and reads the element as a nonzero endomorphism of `𝒪 ⊕ 𝒪(-1)` on `ℙ¹_ℤ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveGenerator.single_X_mem_endomorphismMatrices`: the matrix
  with `X₀` in position `(0, 1)` and zeroes elsewhere lies in `R`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.single_X_ne_algebraMap`: that matrix is not a
  scalar.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.nontrivial_endomorphismMatrices`: `R` is
  nontrivial.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.not_forall_mem_endomorphismMatrices` and
  `Stacks.AlgebraicGeometry.ProjectiveGenerator.not_mem_endomorphismMatrices_of_degree_two`: the
  homogeneity condition excludes the entry `X₀` on the diagonal of `ℙ⁰_ℤ` and a degree-two entry
  in position `(0, 1)` of `ℙ¹_ℤ`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.matrixRingEquivEnd_single_X_ne_zero`: the
  corresponding endomorphism of `𝒪 ⊕ 𝒪(-1)` is nonzero.

## References

* [Stacks Project, Tag 0CS9](https://stacks.math.columbia.edu/tag/0CS9)
-/

@[expose] public noncomputable section

namespace Stacks.AlgebraicGeometry.ProjectiveGenerator

/-! ### A non-scalar element of the algebra -/

/-- The matrix with `X₀` in position `(0, 1)` and zeroes elsewhere lies in the upper
triangular algebra over `A = ℤ` for `n = 1`: the entry sits in degree `1 - 0 = 1`, and `X₀` is
homogeneous of degree one. -/
public theorem single_X_mem_endomorphismMatrices :
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ))
      ∈ endomorphismMatrices ℤ 1 := by
  rw [mem_endomorphismMatrices]
  intro i j
  by_cases h : (0 : Fin 2) = i ∧ (1 : Fin 2) = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [Matrix.single_apply_same,
      show ((1 : Fin 2) : ℤ) - ((0 : Fin 2) : ℤ) = ((1 : ℕ) : ℤ) by norm_num,
      homogeneousPiece_natCast]
    exact MvPolynomial.isHomogeneous_X _ _
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ h]
    exact zero_mem _

/-- The matrix with `X₀` in position `(0, 1)` is not a scalar matrix, because a scalar matrix
has zeroes off the diagonal and `X₀ ≠ 0`. -/
public theorem single_X_ne_algebraMap (a : ℤ) :
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ))
      ≠ algebraMap ℤ (Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℤ)) a := by
  intro h
  simpa [Matrix.algebraMap_matrix_apply] using congrFun (congrFun h 0) 1

/-- The matrix with `X₀` in position `(0, 1)` is not the zero matrix. -/
public theorem single_X_ne_zero :
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ)) ≠ 0 := by
  intro h
  simpa using congrFun (congrFun h 0) 1

/-- The upper triangular algebra of [Stacks, Tag 0CS9] over `ℤ` for `n = 1` is nontrivial. -/
public theorem nontrivial_endomorphismMatrices :
    Nontrivial (↥(endomorphismMatrices ℤ 1)) :=
  ⟨⟨⟨_, single_X_mem_endomorphismMatrices⟩, 0,
    fun h => single_X_ne_zero (by simpa using congrArg Subtype.val h)⟩⟩

/-! ### Matrices outside the algebra -/

/-- Not every matrix over `S` lies in the algebra: for `n = 0`, where the algebra is the single
entry `S₀ = A`, the matrix with entry `X₀` is excluded, because `X₀` is homogeneous of degree one
and a nonzero polynomial is homogeneous in at most one degree. -/
public theorem not_forall_mem_endomorphismMatrices :
    ¬ (∀ M : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) ℤ), M ∈ endomorphismMatrices ℤ 0) := by
  intro h
  have hm := (mem_endomorphismMatrices ℤ 0).1
    (h (Matrix.of fun _ _ => (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℤ))) 0 0
  rw [show ((0 : Fin 1) : ℤ) - ((0 : Fin 1) : ℤ) = ((0 : ℕ) : ℤ) by norm_num,
    homogeneousPiece_natCast] at hm
  exact one_ne_zero (MvPolynomial.IsHomogeneous.inj_right
    (MvPolynomial.isHomogeneous_X ℤ (0 : Fin 1)) hm (MvPolynomial.X_ne_zero 0))

/-- A degree-`2` entry in position `(0, 1)`, where the algebra has `S₁`, is excluded: `X₀²` is
homogeneous of degree two, and a nonzero polynomial is homogeneous in at most one degree. -/
public theorem not_mem_endomorphismMatrices_of_degree_two :
    ¬ (Matrix.single (0 : Fin 2) (1 : Fin 2)
        (MvPolynomial.X 0 * MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ)
      ∈ endomorphismMatrices ℤ 1) := by
  intro h
  have hm := (mem_endomorphismMatrices ℤ 1).1 h 0 1
  rw [Matrix.single_apply_same,
    show ((1 : Fin 2) : ℤ) - ((0 : Fin 2) : ℤ) = ((1 : ℕ) : ℤ) by norm_num,
    homogeneousPiece_natCast] at hm
  have := ((MvPolynomial.isHomogeneous_X ℤ 0).mul (MvPolynomial.isHomogeneous_X ℤ 0)).inj_right
    hm (mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 0))
  omega

/-- The endomorphism of `𝒪 ⊕ 𝒪(-1)` on `ℙ¹_ℤ` attached to the matrix with `X₀` in position
`(0, 1)` is nonzero. -/
public theorem matrixRingEquivEnd_single_X_ne_zero :
    matrixRingEquivEnd ℤ 1 ⟨_, single_X_mem_endomorphismMatrices⟩ ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (matrixRingEquivEnd ℤ 1).injective]
  exact fun h => single_X_ne_zero (congrArg Subtype.val h)

end Stacks.AlgebraicGeometry.ProjectiveGenerator

end
