module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowup
public import StacksFrontier.RingTheory.ReesAlgebra.VariablePresentation

/-!
# The Rees algebra of the coordinate centre in affine space

Fix a commutative ring `R` and integers `m, n ≥ 0`, and write affine `(m + n)`-space over `R` as
`Spec A` with `A = R[x₁, …, x_m, y₁, …, y_n]`, the polynomial ring on `Fin m ⊕ Fin n`. The ideal
`(y₁, …, y_n)` is `Stacks.MoreMorphisms.coordinateRingIdeal`, and its Rees algebra is
`A[T₁, …, T_n]/(y_i T_j − y_j T_i)`, with `T_i` mapping to the degree-one element `y_i`.

## Main results

* `Stacks.MoreMorphisms.exists_coordinateReesPresentation`: the Rees algebra of
  `coordinateRingIdeal R m n` is `A[T₁, …, T_n]/(y_i T_j − y_j T_i)`, by an isomorphism of
  `A`-algebras carrying `T_i` to the degree-one element `y_i` of `A[X]`.

## Implementation notes

The result is the instance `v = Sum.inr : Fin n → Fin m ⊕ Fin n` of
`Stacks.ReesAlgebra.exists_reesPresentation`: `coordinateRingIdeal R m n` is by definition
`Stacks.ReesAlgebra.variableIdeal Sum.inr`, and the ideal of Koszul relations displayed here is
by definition `Stacks.ReesAlgebra.koszulIdeal Sum.inr`.

## References

* [Stacks Project, Tag 0H1H](https://stacks.math.columbia.edu/tag/0H1H)
-/

@[expose] public section

open MvPolynomial

namespace Stacks.MoreMorphisms

variable (R : Type*) [CommRing R] (m n : ℕ)

/-- The Rees algebra of `A = R[x₁,…,x_m,y₁,…,y_n]` with respect to the ideal `(y₁,…,y_n)` is
`A[T₁,…,T_n]/(y_i T_j − y_j T_i)`, with `T_i` going to the degree-one element `y_i`. -/
@[stacks 0H1H "the Rees algebra is A[T]/(y_i T_j - y_j T_i)"]
public theorem exists_coordinateReesPresentation :
    ∃ E : (MvPolynomial (Fin n) (MvPolynomial (Fin m ⊕ Fin n) R) ⧸
        Ideal.span (Set.range fun p : Fin n × Fin n ↦
          C (X (Sum.inr p.1)) * X p.2 - C (X (Sum.inr p.2)) * X p.1))
        ≃ₐ[MvPolynomial (Fin m ⊕ Fin n) R] reesAlgebra (coordinateRingIdeal R m n),
      ∀ j : Fin n,
        (E (Ideal.Quotient.mk _ (X j)) : Polynomial (MvPolynomial (Fin m ⊕ Fin n) R)) =
          Polynomial.monomial 1 (X (Sum.inr j)) :=
  Stacks.ReesAlgebra.exists_reesPresentation (R := R) (Sum.inr : Fin n → Fin m ⊕ Fin n)
    Sum.inr_injective

end Stacks.MoreMorphisms

end
