module

public import StacksFrontier.RingTheory.Etale.DirectedColimitPresentation

/-!
# Étaleness of a standard presentation survives pushing its coefficients along a ring map

A standard presentation `R[x₁, …, x_n] ⧸ (P₁, …, P_n)` which is étale over `R` stays étale after
its coefficients are pushed along a ring map `R ⟶ T`: the presented ring base-changes to the
presented ring of the pushed system, by `Algebra.tensorQuotientSpanEquiv`, and étaleness is stable
under base change.

## Main results

* `Algebra.etale_mvPolynomialQuotientMap_of_etale` — the base change, as an instance-producing
  theorem: if `R[x] ⧸ (v)` is étale over `R` then `T[x] ⧸ (v^{algebraMap})` is étale over `T`.
* `Algebra.etale_mvPolynomialQuotientMap_of_etale_ringHom` — the same for a bare ring homomorphism
  `ψ : R →+* T`, with the `R`-algebra structure on `T` taken to be `ψ`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public noncomputable section

open TensorProduct

universe v u

namespace Algebra

/-- **Étaleness of a standard presentation is stable under pushing the coefficients along the
structure map of an algebra.**  If the quotient `R[x] ⧸ (v)` of a polynomial ring by a family of
relations is étale over `R`, then the quotient of `T[x]` by the coefficientwise images of the same
relations is étale over `T`. -/
theorem etale_mvPolynomialQuotientMap_of_etale (R : Type u) [CommRing R] (T : Type v) [CommRing T]
    [Algebra R T] {ιp : Type*} {σ : Type*} (v : ιp → MvPolynomial σ R)
    [Algebra.Etale R (MvPolynomial σ R ⧸ Ideal.span (Set.range v))] :
    Algebra.Etale T (MvPolynomial σ T ⧸
      Ideal.span (Set.range fun k ↦ MvPolynomial.map (algebraMap R T) (v k))) :=
  Algebra.Etale.of_equiv (tensorQuotientSpanEquiv R T v)

/-- **Étaleness of a standard presentation is stable under pushing the coefficients along a ring
homomorphism.**  If `R[x] ⧸ (v)` is étale over `R` and `ψ : R →+* T` is a ring homomorphism,
then the quotient of `T[x]` by the images of the relations under `ψ` is étale over `T`, where `T`
is an `R`-algebra via `ψ`. -/
theorem etale_mvPolynomialQuotientMap_of_etale_ringHom {R : Type u} [CommRing R] {T : Type u}
    [CommRing T] (ψ : R →+* T) {ιp : Type*} {σ : Type*} (v : ιp → MvPolynomial σ R)
    [Algebra.Etale R (MvPolynomial σ R ⧸ Ideal.span (Set.range v))] :
    letI := ψ.toAlgebra
    Algebra.Etale T (MvPolynomial σ T ⧸ Ideal.span (Set.range fun k ↦ MvPolynomial.map ψ (v k))) :=
  let := ψ.toAlgebra
  etale_mvPolynomialQuotientMap_of_etale R T v

end Algebra

end
