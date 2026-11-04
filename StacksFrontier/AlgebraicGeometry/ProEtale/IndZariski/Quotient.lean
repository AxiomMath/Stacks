module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Ind-Zariski algebras modulo an ideal of the base

Reducing an ind-Zariski algebra modulo the extension of an ideal of its base ring gives an
ind-Zariski algebra over the quotient of the base.

## Main results

* `AlgebraicGeometry.ProEtale.isIndZariski_quotient`: if `B` is ind-Zariski over `A` and `I` is
  an ideal of `A`, then `B ⧸ I·B` is ind-Zariski over `A ⧸ I`.

## Implementation notes

This is the base change of `A → B` along `A → A ⧸ I`, since `B ⧸ I·B` is `(A ⧸ I) ⊗[A] B` by
Mathlib's `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`; the statement is therefore
obtained from stability of the ind-Zariski property under base change, transported along that
isomorphism. The algebra structure of `B ⧸ I·B` over `A ⧸ I` is Mathlib's instance
`Ideal.Quotient.algebraQuotientMapQuotient`, whose structure map is the quotient of
`algebraMap A B`.

## References

* [Stacks Project, Tag 096P](https://stacks.math.columbia.edu/tag/096P)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u v

/-- The quotient of an ind-Zariski algebra by the extension of an ideal of the base ring is
ind-Zariski over the quotient of the base ring by that ideal. -/
theorem isIndZariski_quotient (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (h : Algebra.IsIndZariski A B) :
    Algebra.IsIndZariski (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  Algebra.IsIndZariski.of_equiv (RingEquiv.refl (A ⧸ I))
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toRingEquiv
    (fun a ↦ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.commutes a)
    (Algebra.IsIndZariski.tensorProduct' A B (A ⧸ I) h)

end AlgebraicGeometry.ProEtale

end
