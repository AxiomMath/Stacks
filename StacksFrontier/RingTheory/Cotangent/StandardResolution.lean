module

public import StacksFrontier.Cotangent.StandardResolution
public import StacksFrontier.AlgebraicTopology.StandardResolution.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Polynomiality of the terms of the standard resolution

For a commutative ring `A` and a commutative `A`-algebra `B`, the standard augmented simplicial
resolution `P• ⟶ B` of **Stacks 08PM** is `CommAlgCat.standardResolution`, whose terms are the
iterated polynomial algebras `A[B]`, `A[A[B]]`, and so on. This file contributes the unbundled
polynomiality predicate the cotangent-complex files state their hypotheses with, and the fact
that every term of the standard resolution satisfies it.

## Main definitions

* `Algebra.IsPolynomialAlgebra`: an `A`-algebra isomorphic to a polynomial algebra over `A`.

## Main results

* `CommAlgCat.standardResolution_obj_isPolynomialAlgebra`: every term is a polynomial algebra
  over `A` — condition (1) of a resolution in the sense of **Stacks 08QI**.

## Implementation notes

The resolution itself — `CommAlgCat.free`, `adj`, `polynomialComonad`, `standardEndofunctor`,
`standardResolution`, `standardResolutionFunctor`, `standardResolutionZeroAlgEquiv`,
`standardResolutionAugmentation` and their term, face, degeneracy and augmentation equations —
together with its computational interface in low degrees (`standardResolutionVarZero`,
`standardResolutionVarOne`, the two face equations, the identification of every term with a
polynomial algebra and surjectivity of the augmentation) is imported from
`StacksFrontier.Cotangent.StandardResolution`, which carries **Stacks 08PM**. This file once
constructed all of that a second time; the two constructions were definitionally equal, so the
duplicate was retired in favour of the import and every name used below means exactly what it
meant before.

`Algebra.IsPolynomialAlgebra` is named away from `CommAlgCat`, where
`StacksFrontier.Cotangent.Resolution` declares a different statement under that name: that one
takes a bundled object of `CommAlgCat A` where this one takes an unbundled `A`-algebra.
Likewise `CommAlgCat.standardResolution_obj_isPolynomialAlgebra` is the absolute statement that
every term of the standard resolution is a polynomial algebra over `A`, where
`CommAlgCat.standardResolution_isPolynomialAlgebra` of
`StacksFrontier.Cotangent.Triangle.BaseChange` is the relative polynomiality of one standard
resolution over another along an injective algebra map.

## References

* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v

namespace Algebra

/-- A commutative `A`-algebra is a polynomial algebra over `A` if it is isomorphic, as an
`A`-algebra, to a multivariate polynomial algebra over `A`. -/
public abbrev IsPolynomialAlgebra (A : Type u) [CommRing A] (P : Type v) [CommRing P]
    [_root_.Algebra A P] : Prop :=
  ∃ ι : Type v, Nonempty (MvPolynomial ι A ≃ₐ[A] P)

end Algebra

namespace CommAlgCat

/-! ### Polynomiality of every term -/

/-- **Condition (1) of a resolution (Stacks 08QI).** Every term of the standard resolution is a
polynomial algebra over `A`. -/
public theorem standardResolution_obj_isPolynomialAlgebra (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ) :
    Algebra.IsPolynomialAlgebra A ((standardResolution A B).left.obj n) := by
  refine ⟨(((polynomialComonad.{u, v} A).toFunctor.iterate n.unop.len).obj B), ⟨?_⟩⟩
  have hn : n = op ⦋n.unop.len⦌ := by rw [SimplexCategory.mk_len]
  rw [hn, standardResolution_obj_mvPolynomial]
  exact AlgEquiv.refl

end CommAlgCat

end
