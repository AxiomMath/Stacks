module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# A polynomial ring is generated in degree one

A polynomial ring, graded by total degree, is generated over its degree-zero part by its
degree-one part.

## Main results

* `Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule`: the degree-one
  homogeneous polynomials generate `MvPolynomial ι K` as an algebra over the degree-zero
  homogeneous polynomials.

## Implementation notes

The statement is about the whole degree-one piece, not only about the variables.

The grading is an instance argument rather than a `letI` inside the statement:
`MvPolynomial.gradedAlgebra` is not a global instance, so a caller introduces it by `letI`, and
that `letI` is then the instance argument, with no `let` to unfold in the statement. Since
`GradedAlgebra` is reducibly `GradedRing`, a caller holding `GradedAlgebra` supplies it directly.

No tag attribute is attached: this is an algebra fact with no tag of its own.
-/
@[expose] public section

universe u v

namespace Stacks.AlgebraicGeometry.TwistFlatness

/-- **A polynomial ring is generated in degree one** over its degree-zero part: the degree-one
homogeneous polynomials generate `MvPolynomial ι K` as an algebra over the degree-zero ones. -/
theorem adjoin_degree_one_homogeneousSubmodule (ι : Type v) (K : Type u) [CommRing K]
    [GradedRing (MvPolynomial.homogeneousSubmodule ι K)] :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule ι K 0)
      (Set.range fun f : MvPolynomial.homogeneousSubmodule ι K 1 =>
        (f : MvPolynomial ι K)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _
      (⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C ι a⟩ :
        MvPolynomial.homogeneousSubmodule ι K 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp =>
    exact mul_mem hp
      (Algebra.subset_adjoin ⟨⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩, rfl⟩)

end Stacks.AlgebraicGeometry.TwistFlatness

end
