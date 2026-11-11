module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEquivalenceLinear
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorHomGroups

/-!
# Beilinson's equivalence over the upper triangular matrix algebra

Let `A` be a ring, `X = P^n_A = Proj A[X₀, …, Xₙ]` and `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`.
[Stacks, Equation 0CS9] defines `R = Hom_{𝒪_X}(P, P)` and describes it as the ring of upper
triangular `(n + 1) × (n + 1)` matrices whose `(i, j)` entry is homogeneous of degree `j - i` in
`S = A[X₀, …, Xₙ]`. The source category `D(R)` of Beilinson's equivalence is formed for the
differential graded algebra `Hom_{Comp^dg(𝒪_X)}(P, P)` with zero differential
(`Stacks.AlgebraicGeometry.Beilinson.endAlgebra`). This file identifies its ring with the matrix
algebra `Stacks.AlgebraicGeometry.ProjectiveGenerator.endomorphismMatrices`, and states
[Stacks, Tag 0BQU] in full with that identification.

## Main definitions

* `Stacks.AlgebraicGeometry.Beilinson.endAlgebraRingEquivMatrices`: the ring of
  `Hom^dg(P, P)` is the upper triangular matrix algebra of Tag 0CS9.

## Main results

* `Stacks.AlgebraicGeometry.Beilinson.beilinson_equivalence_matrixAlgebra`: [Stacks, Tag 0BQU].

## References

* [Stacks Project, Tag 0BQU](https://stacks.math.columbia.edu/tag/0BQU)
* [Stacks Project, Tag 0CS9](https://stacks.math.columbia.edu/tag/0CS9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumQCoh)
open Stacks.AlgebraicGeometry.ProjectiveGenerator (endomorphismMatrices matrixRingEquivEnd)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.Beilinson

variable (A : Type u) [CommRing A] (n : ℕ)

/-- **The ring of `R = Hom^dg(P, P)` is the upper triangular matrix algebra of Tag 0CS9**: the
degree-zero component identifies it with `End P = Hom_{𝒪_X}(P, P)`
(`Stacks.AlgebraicGeometry.Beilinson.endAlgebraRingEquiv`), and `End P` is the ring of
`(n + 1) × (n + 1)` matrices over `A[X₀, …, Xₙ]` whose `(i, j)` entry is homogeneous of degree
`j - i` (`Stacks.AlgebraicGeometry.ProjectiveGenerator.matrixRingEquivEnd`). -/
def endAlgebraRingEquivMatrices : (endAlgebra A n).A ≃+* endomorphismMatrices A n :=
  (endAlgebraRingEquiv A n).trans (matrixRingEquivEnd A n).symm

/-- **[Stacks, Tag 0BQU] (Beilinson).** Let `A` be a ring, `X = P^n_A = Proj A[X₀, …, Xₙ]`,
`P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` as in Tag 0CS8, and `R = Hom_{𝒪_X}(P, P)` as in Tag 0CS9,
viewed as the differential graded algebra `Hom_{Comp^dg(𝒪_X)}(P, P)` with zero differential.
Then `- ⊗_R^𝐋 P : D(R) ⥤ D_QCoh(𝒪_X)` is an equivalence of categories, is exact, sends `R` to
`P`, and is `A`-linear (for `A ⊂ center(R)` acting on `D(R)` and `A → Γ(X, 𝒪_X)` acting on
`D_QCoh(𝒪_X)`); and the ring of `R` is the upper triangular algebra of matrices over
`A[X₀, …, Xₙ]` with `(i, j)` entry homogeneous of degree `j - i`. -/
@[stacks 0BQU "Beilinson's equivalence - ⊗_R^L P : D(R) → D_QCoh(O_X) on X = P^n_A, with \
P = O_X ⊕ O_X(-1) ⊕ ... ⊕ O_X(-n) of Tag 0CS8 and R = Hom_{O_X}(P, P) of Tag 0CS9 read as the \
differential graded algebra Hom^dg(P, P) with zero differential: an equivalence, exact, \
A-linear, sending R to P, with the ring of R identified with the upper triangular matrix \
algebra of Tag 0CS9 by endAlgebraRingEquivMatrices"]
theorem beilinson_equivalence_matrixAlgebra :
    ((tensorWithGenerator A n).IsEquivalence ∧ (tensorWithGenerator A n).IsTriangulated ∧
      Nonempty ((tensorWithGenerator A n).obj (regular A n) ≅ twistSumQCoh A n) ∧
      letI := derivedCategoryRLinear A n
      letI := quasiCoherentDerivedCategoryLinear A n
      (tensorWithGenerator A n).Linear A) ∧
      Nonempty ((endAlgebra A n).A ≃+* endomorphismMatrices A n) :=
  ⟨beilinson_equivalence A n, ⟨endAlgebraRingEquivMatrices A n⟩⟩

end Stacks.AlgebraicGeometry.Beilinson

end
