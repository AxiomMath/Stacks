module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology

/-! # Degree-lowering graded derivations

A *graded derivation* of degree minus one on a nonnegatively graded algebra lowers degree by one,
vanishes in degree zero, and satisfies the signed Leibniz rule. These are the axioms of
`DividedPowers.TateResolution.IsDifferentialGradedAlgebra` with the square-zero condition
dropped.

The square-zero condition is what fails for the lifted operator of Tag 09PS: there the
differential of a divided power differential graded algebra over `R` is lifted across a surjection
`R' → R` with square-zero principal kernel, and the square of the lift is precisely the
degree-minus-two derivation the tag constructs. Every statement about the one-variable extensions
of Tags 09PH and 09PI that does not mention the square of the differential holds for a graded
derivation, so separating the axioms lets those statements be used on the lift.

## Main definitions

* `DividedPowers.TateResolution.IsGradedDerivation` — the differential graded algebra axioms
  without `d_sq_zero`.

## Main results

* `DividedPowers.TateResolution.IsDifferentialGradedAlgebra.toIsGradedDerivation` — a differential
  graded algebra is in particular a graded derivation.
* `DividedPowers.TateResolution.IsGradedDerivation.of_d_sq_zero` — conversely, a graded derivation
  whose square vanishes is a differential graded algebra.

## References

* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- A degree-minus-one graded derivation: it vanishes in degree zero, lowers every positive
degree by one, and satisfies the signed Leibniz rule on homogeneous elements. These are the
axioms of a differential graded algebra without the square-zero condition. -/
public class IsGradedDerivation (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : A →ₗ[R] A) : Prop where
  /-- The derivation vanishes in degree zero. -/
  d_grade_zero : ∀ {x : A}, x ∈ 𝒜 0 → d x = 0
  /-- The derivation lowers every positive degree by one. -/
  d_mem : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 (n + 1) → d x ∈ 𝒜 n
  /-- The derivation satisfies the signed Leibniz rule on homogeneous elements. -/
  leibniz : ∀ {i j : ℕ} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
    d (x * y) = d x * y + (-1 : R) ^ i • (x * d y)

/-- A differential graded algebra is in particular a graded derivation. -/
public instance IsDifferentialGradedAlgebra.toIsGradedDerivation (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d] :
    IsGradedDerivation 𝒜 d where
  d_grade_zero := IsDifferentialGradedAlgebra.d_grade_zero
  d_mem := IsDifferentialGradedAlgebra.d_mem
  leibniz := IsDifferentialGradedAlgebra.leibniz

/-- A graded derivation whose square vanishes is a differential graded algebra. -/
public theorem IsGradedDerivation.of_d_sq_zero (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] (d : A →ₗ[R] A) [IsGradedDerivation 𝒜 d]
    (hsq : ∀ x : A, d (d x) = 0) : IsDifferentialGradedAlgebra 𝒜 d where
  d_grade_zero := IsGradedDerivation.d_grade_zero
  d_mem := IsGradedDerivation.d_mem
  d_sq_zero := hsq
  leibniz := IsGradedDerivation.leibniz

end DividedPowers.TateResolution

end
