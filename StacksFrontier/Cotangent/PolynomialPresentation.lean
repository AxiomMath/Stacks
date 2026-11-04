module

public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Polynomial presentations with chosen kernel generators

Given a homomorphism of commutative rings, this file records a presentation of its target as a
quotient of a polynomial ring, together with a chosen family generating the kernel of the
presentation map. This is the data from which the Lichtenbaum–Schlessinger complex of Stacks
92.13 is built, and the situation in which the length-two resolutions of Stacks 92.5 are
described.

## Main definitions

* `Algebra.PolynomialPresentationWithKernelGenerators`: a polynomial presentation of a ring map
  together with a chosen generating family for the kernel.
* `Algebra.PolynomialPresentationWithKernelGenerators.P0`: the polynomial ring occurring in such
  a presentation.

## Implementation notes

The polynomial variables and the kernel generators are allowed to be indexed by arbitrary types,
as in the source. Mathlib's `Algebra.Presentation` packages the surjective polynomial map and
the assertion that the chosen relations generate its kernel.

## References

* [Stacks Project, Tag 09D4](https://stacks.math.columbia.edu/tag/09D4)
-/

@[expose] public section

universe u v w x

namespace Algebra

/-- A presentation of a ring homomorphism `A →+* B` by a polynomial ring `A[u_i]`,
together with a chosen family `f_t` generating the kernel of the presentation map. -/
structure PolynomialPresentationWithKernelGenerators where
  /-- The source of the given ring homomorphism. -/
  A : Type u
  /-- The target of the given ring homomorphism. -/
  B : Type v
  /-- The commutative-ring structure on the source. -/
  [commRingA : CommRing A]
  /-- The commutative-ring structure on the target. -/
  [commRingB : CommRing B]
  /-- The given ring homomorphism `A → B`. -/
  algebraMap : A →+* B
  /-- The indexing type for the polynomial variables `u_i`. -/
  variableIndex : Type w
  /-- The indexing type for the chosen kernel generators. -/
  relationIndex : Type x
  /-- The surjective polynomial presentation, together with the chosen generators of its
  kernel. -/
  presentation :
    @Algebra.Presentation A B variableIndex relationIndex _ _ algebraMap.toAlgebra

attribute [instance]
  PolynomialPresentationWithKernelGenerators.commRingA
  PolynomialPresentationWithKernelGenerators.commRingB

namespace PolynomialPresentationWithKernelGenerators

/-- The polynomial ring `P₀ = A[u_i]` of a polynomial presentation. -/
abbrev P0 (presentation : PolynomialPresentationWithKernelGenerators.{u, v, w, x}) :=
  letI := presentation.algebraMap.toAlgebra
  presentation.presentation.Ring

end PolynomialPresentationWithKernelGenerators

end Algebra

end
