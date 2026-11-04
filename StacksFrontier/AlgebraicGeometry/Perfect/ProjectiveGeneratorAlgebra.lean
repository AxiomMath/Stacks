module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Projective
public import StacksCore.Tactic.StacksAttribute

/-!
# The twist sum on projective space and the upper triangular algebra of its endomorphisms

Let `A` be a commutative ring, let `X = ℙⁿ_A` and let `S = A[X₀, …, Xₙ]`. The object

`P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`

is the direct sum of the `n + 1` nonpositive twists of the structure sheaf. Its endomorphism ring
is the ring of upper triangular `(n + 1) × (n + 1)` matrices over `S` whose `(i, j)` entry is
homogeneous of degree `j - i`: the diagonal carries `S₀`, the first superdiagonal `S₁`, the second
`S₂`, and so on, while every entry strictly below the diagonal vanishes.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveGenerator.homogeneousPiece`: the degree-`d` homogeneous part
  `S_d` of `A[X₀, …, Xₙ]` for an integer `d`, taken to be zero in negative degrees.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.twistSum`: the direct sum
  `𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` of twists on `ℙⁿ_A`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.endomorphismMatrices`: the `A`-subalgebra of
  `(n + 1) × (n + 1)` matrices over `A[X₀, …, Xₙ]` whose `(i, j)` entry lies in `S_{j - i}`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveGenerator.mul_mem_homogeneousPiece`: the homogeneous pieces
  multiply additively in the degree, including the negative degrees.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.mem_endomorphismMatrices`: a matrix belongs to the
  algebra precisely when each `(i, j)` entry is homogeneous of degree `j - i`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.apply_eq_zero_of_lt`: such a matrix vanishes
  strictly below the diagonal, so it is upper triangular.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.isHomogeneous_apply`: on and above the diagonal
  the `(i, j)` entry is homogeneous of degree `j - i` as a natural number.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.exists_C_diag`: the diagonal entries are the
  constants `S₀ = A`.

## Implementation notes

The twists are indexed by `i : Fin (n + 1)` at the degrees `-i`, so the summand at `i = 0` is the
zeroth twist `𝒪_X(0)` rather than the structure sheaf on the nose; the direct sum is the finite
coproduct in the category of `𝒪_X`-modules.

Extending the grading of `A[X₀, …, Xₙ]` to all integer degrees by zero is what makes the single
condition "the `(i, j)` entry lies in `S_{j - i}`" express both the homogeneity above the diagonal
and the vanishing below it, so that membership in the algebra is that one condition and nothing
else.

The identification of the endomorphism ring of the twist sum with `endomorphismMatrices`,
[Stacks, Tag 0CS9], is `Stacks.AlgebraicGeometry.ProjectiveGenerator.matrixRingEquivEnd` in
`StacksFrontier/AlgebraicGeometry/Perfect/ProjectiveGeneratorHomGroups.lean`, where the twist sum is
formed on `Proj A[X₀, …, Xₙ]`.

## References

* [Stacks Project, Tag 0CS8](https://stacks.math.columbia.edu/tag/0CS8)
* [Stacks Project, Tag 0CS9](https://stacks.math.columbia.edu/tag/0CS9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveGenerator

variable (A : Type u) [CommRing A] (n : ℕ)

/-! ### The homogeneous pieces of the polynomial ring -/

/-- The degree-`d` homogeneous part `S_d` of `S = A[X₀, …, Xₙ]`, for an integer degree `d`; it is
the zero submodule when `d` is negative. -/
public def homogeneousPiece (d : ℤ) : Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  if 0 ≤ d then MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d.toNat else ⊥

/-- In nonnegative degrees the integer-indexed piece is the usual homogeneous component. -/
public theorem homogeneousPiece_of_nonneg {d : ℤ} (hd : 0 ≤ d) :
    homogeneousPiece A n d = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d.toNat := by
  simp [homogeneousPiece, hd]

/-- There are no nonzero polynomials of negative degree. -/
public theorem homogeneousPiece_of_neg {d : ℤ} (hd : d < 0) : homogeneousPiece A n d = ⊥ := by
  simp [homogeneousPiece, not_le.2 hd]

/-- At a natural-number degree the integer-indexed piece is the usual homogeneous component. -/
@[simp] public theorem homogeneousPiece_natCast (d : ℕ) :
    homogeneousPiece A n (d : ℤ) = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d := by
  simp [homogeneousPiece]

/-- A homogeneous polynomial of degree zero lies in the degree-zero piece. -/
private theorem mem_homogeneousPiece_zero {p : MvPolynomial (Fin (n + 1)) A}
    (hp : p.IsHomogeneous 0) : p ∈ homogeneousPiece A n 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, homogeneousPiece_natCast]
  exact hp

/-- The unit of `S` is homogeneous of degree zero. -/
public theorem one_mem_homogeneousPiece :
    (1 : MvPolynomial (Fin (n + 1)) A) ∈ homogeneousPiece A n 0 :=
  mem_homogeneousPiece_zero A n (MvPolynomial.isHomogeneous_one _ _)

/-- The constants of `S` are homogeneous of degree zero. -/
public theorem C_mem_homogeneousPiece (a : A) :
    (MvPolynomial.C a : MvPolynomial (Fin (n + 1)) A) ∈ homogeneousPiece A n 0 :=
  mem_homogeneousPiece_zero A n (MvPolynomial.isHomogeneous_C _ _)

/-- Multiplying a polynomial of degree `c` by one of degree `d` gives one of degree `c + d`, in
every pair of integer degrees. -/
public theorem mul_mem_homogeneousPiece {c d : ℤ} {p q : MvPolynomial (Fin (n + 1)) A}
    (hp : p ∈ homogeneousPiece A n c) (hq : q ∈ homogeneousPiece A n d) :
    p * q ∈ homogeneousPiece A n (c + d) := by
  rcases lt_or_ge c 0 with hc | hc
  · rw [homogeneousPiece_of_neg A n hc, Submodule.mem_bot] at hp
    simp [hp]
  rcases lt_or_ge d 0 with hd | hd
  · rw [homogeneousPiece_of_neg A n hd, Submodule.mem_bot] at hq
    simp [hq]
  rw [homogeneousPiece_of_nonneg A n hc] at hp
  rw [homogeneousPiece_of_nonneg A n hd] at hq
  rw [homogeneousPiece_of_nonneg A n (by omega : (0 : ℤ) ≤ c + d),
    show (c + d).toNat = c.toNat + d.toNat by omega]
  exact MvPolynomial.IsHomogeneous.mul hp hq

/-! ### The sum of the twists -/

/-- The direct sum `𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` of the `n + 1` nonpositive twists of the
structure sheaf of `X = ℙⁿ_A`. -/
@[stacks 0CS8]
public def twistSum : (projectiveSpaceOverRing n (.of A)).Modules :=
  ∐ fun i : Fin (n + 1) => ProjTwistFunctor.projectiveTwistingSheaf (R := A) n (-(i : ℤ))

/-! ### The upper triangular algebra of homogeneous matrices -/

/-- The `A`-subalgebra of `(n + 1) × (n + 1)` matrices over `S = A[X₀, …, Xₙ]` whose `(i, j)`
entry is homogeneous of degree `j - i`: the diagonal carries `S₀`, the first superdiagonal `S₁`,
and so on, with zero strictly below the diagonal. -/
public def endomorphismMatrices :
    Subalgebra A (Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) A)) where
  carrier := {M | ∀ i j : Fin (n + 1), M i j ∈ homogeneousPiece A n ((j : ℤ) - (i : ℤ))}
  mul_mem' := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    refine sum_mem fun k _ => ?_
    have h := mul_mem_homogeneousPiece A n (hM i k) (hN k j)
    rwa [show ((k : ℤ) - (i : ℤ)) + ((j : ℤ) - (k : ℤ)) = (j : ℤ) - (i : ℤ) by ring] at h
  one_mem' := by
    intro i j
    rcases eq_or_ne i j with rfl | h
    · rw [Matrix.one_apply_eq, show ((i : ℤ) - (i : ℤ)) = 0 by ring]
      exact one_mem_homogeneousPiece A n
    · rw [Matrix.one_apply_ne h]
      exact zero_mem _
  add_mem' := fun hM hN i j => add_mem (hM i j) (hN i j)
  zero_mem' := fun _ _ => zero_mem _
  algebraMap_mem' := by
    intro a i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs with h
    · subst h
      rw [show ((i : ℤ) - (i : ℤ)) = 0 by ring]
      exact C_mem_homogeneousPiece A n a
    · exact zero_mem _

/-- A matrix lies in the algebra precisely when its `(i, j)` entry is homogeneous of degree
`j - i`, negative degrees contributing only zero. -/
public theorem mem_endomorphismMatrices
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) A)} :
    M ∈ endomorphismMatrices A n ↔
      ∀ i j : Fin (n + 1), M i j ∈ homogeneousPiece A n ((j : ℤ) - (i : ℤ)) := Iff.rfl

/-- A matrix of the algebra is upper triangular: it vanishes strictly below the diagonal. -/
public theorem apply_eq_zero_of_lt
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) A)}
    (hM : M ∈ endomorphismMatrices A n) {i j : Fin (n + 1)} (hji : j < i) : M i j = 0 := by
  have h := hM i j
  have hlt : (j : ℤ) - (i : ℤ) < 0 := by
    have hn : (j : ℕ) < (i : ℕ) := hji
    omega
  rwa [homogeneousPiece_of_neg A n hlt, Submodule.mem_bot] at h

/-- On and above the diagonal, the `(i, j)` entry of a matrix of the algebra is a homogeneous
polynomial of degree `j - i`. -/
public theorem isHomogeneous_apply
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) A)}
    (hM : M ∈ endomorphismMatrices A n) {i j : Fin (n + 1)} (hij : i ≤ j) :
    (M i j).IsHomogeneous ((j : ℕ) - (i : ℕ)) := by
  have h := hM i j
  have hle : (i : ℕ) ≤ (j : ℕ) := hij
  rw [show (j : ℤ) - (i : ℤ) = (((j : ℕ) - (i : ℕ) : ℕ) : ℤ) by omega,
    homogeneousPiece_natCast] at h
  exact h

/-- The diagonal entries of a matrix of the algebra are the constants `S₀ = A`. -/
public theorem exists_C_diag
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) A)}
    (hM : M ∈ endomorphismMatrices A n) (i : Fin (n + 1)) :
    ∃ a : A, M i i = MvPolynomial.C a := by
  have h := hM i i
  rw [show ((i : ℤ) - (i : ℤ)) = ((0 : ℕ) : ℤ) by ring, homogeneousPiece_natCast,
    MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by rw [← ha, MvPolynomial.algebraMap_eq]⟩

end Stacks.AlgebraicGeometry.ProjectiveGenerator

end
