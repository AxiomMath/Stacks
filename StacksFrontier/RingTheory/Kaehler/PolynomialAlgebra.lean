module

public import StacksFrontier.Cotangent.DirectedColimit
public import StacksFrontier.RingTheory.Cotangent.StandardResolution

/-!
# Differentials of a polynomial algebra

Let `A` be a commutative ring and let `B` be an `A`-algebra which is a polynomial algebra over
`A`, that is, `Algebra.IsPolynomialAlgebra A B`: there are a type `ι` of variables and an
isomorphism of `A`-algebras `A[ι] ≃ₐ[A] B`. The module of Kähler differentials `Ω[B⁄A]` is then
free over `B`, on the differentials of the images of the variables, and in particular projective.

## Main results

* `KaehlerDifferential.free_of_isPolynomialAlgebra`: `Ω[B⁄A]` is a free `B`-module.
* `KaehlerDifferential.projective_of_isPolynomialAlgebra`: `Ω[B⁄A]` is a projective `B`-module.

## Implementation notes

Mathlib's `KaehlerDifferential.mvPolynomialBasis` is a basis of `Ω[A[ι]⁄A]` over `A[ι]`, so
transporting it along `A[ι] ≃ₐ[A] B` changes the ring of scalars as well as the module. The
transport is `KaehlerDifferential.basisOfMvPolynomialAlgEquiv`, which combines
`Module.Basis.mapCoeffs` for the change of coefficients with the functoriality
`KaehlerDifferential.map` of `Ω` in the pair of rings for the change of module.

## References

* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH), the cotangent complex
  of a polynomial algebra.
* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA).
-/

@[expose] public section

universe u v

/-- The module of differentials of a polynomial algebra `B` over `A` is a free `B`-module, on
the differentials of the images of the polynomial variables. -/
public theorem KaehlerDifferential.free_of_isPolynomialAlgebra {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B] (hB : Algebra.IsPolynomialAlgebra A B) :
    Module.Free B (KaehlerDifferential A B) := by
  obtain ⟨ι, ⟨e⟩⟩ := hB
  exact Module.Free.of_basis (KaehlerDifferential.basisOfMvPolynomialAlgEquiv e.symm)

/-- The module of differentials of a polynomial algebra `B` over `A` is a projective
`B`-module. -/
public theorem KaehlerDifferential.projective_of_isPolynomialAlgebra {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B] (hB : Algebra.IsPolynomialAlgebra A B) :
    Module.Projective B (KaehlerDifferential A B) :=
  have := KaehlerDifferential.free_of_isPolynomialAlgebra hB
  Module.Projective.of_free

end
