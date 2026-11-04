module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Bimodule
public import StacksFrontier.Algebra.DGA.LeftAction

/-!
# Differential graded bimodules, presented by a left action on the underlying complex

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let `M` be a right
differential graded `B`-module. A differential graded `(A, B)`-bimodule structure on `M` is a left
differential graded action of `A` on the complex underlying `M` whose every homogeneous component
is right `B`-linear.

This file states that notion over `DifferentialGradedAlgebra.LeftDGAction`, which carries the
universe of the complex being acted on as a free parameter. That is the generality the Hom-module
constructions of Section 30 are stated in: they take a module whose underlying modules live in
`Type (max u w)` for a `w` independent of the base ring's universe.
`DifferentialGradedModule.BimoduleStructure` is the same notion over
`DifferentialGradedAlgebra.LeftAction`, which goes through an endomorphism differential graded
algebra and therefore pins both the acting algebra and the complex to the base ring's universe;
that version is the one Tag 0FQI's correspondence with right `B`-linear endomorphism
homomorphisms is stated about.

## Main definitions

* `DifferentialGradedModule.DGActionBimoduleStructure`: a left differential graded action of `A`
  on the complex underlying `M`, all of whose homogeneous components are right `B`-linear.

## Implementation notes

Right `B`-linearity of a cochain is `DifferentialGradedModule.IsRightLinearCochain`, which is
already stated at a free module universe, so it is used rather than restated: a homogeneous
right `B`-linear map of the same degree is exhibited agreeing with the cochain on homogeneous
elements. Since the agreement is pinned on every homogeneous element the witness is unique, so
the predicate is a condition on the cochain rather than extra structure.

A bimodule structure is a subtype of the left actions rather than a structure in its own right,
so that forgetting the right-linearity is the first projection and no transport is needed between
the two notions.

## References

* [Stacks Project, Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI)
-/

@[expose] public section

open CategoryTheory CochainComplex.HomComplex

namespace DifferentialGradedModule

universe u v v' w

variable {R : Type u} [CommRing R]
variable (A : DifferentialGradedAlgebra.{u, v} R)
variable (B : DifferentialGradedAlgebra.{u, v'} R)
variable (M : DifferentialGradedModule.{u, v', max u w} B)

/-- A differential graded `(A, B)`-bimodule structure compatible with the fixed right differential
graded `B`-module `M`, presented by a left differential graded action of `A` on the complex
underlying `M`. -/
def DGActionBimoduleStructure : Type _ :=
  { L : DifferentialGradedAlgebra.LeftDGAction A M.toCochainComplex //
    ∀ (n : ℤ) (a : A.grading n), IsRightLinearCochain B M (L.action n a) }

end DifferentialGradedModule

end
