module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The derivative criterion for the conormal map of a polynomial presentation

Let `P` be an algebra over a commutative ring `R` whose module of relative differentials
`Ω[P⁄R]` is free on a basis, and let `I` be an ideal of `P`.  The conormal map of the
presentation `P ⟶ P ⧸ I` carries the class of `f ∈ I` to `1 ⊗ d f`, and this file computes when
that element vanishes: exactly when every coordinate of `d f` in the chosen basis lies in `I`.

For a polynomial algebra the basis is `KaehlerDifferential.mvPolynomialBasis` and the
coordinates of `d f` are the partial derivatives of `f`, so the criterion reads

`1 ⊗ d f = 0 ↔ ∀ i, pderiv i f ∈ I`,

which is the form the naive cotangent complex of a polynomial presentation is computed with:
the degree `-1` cohomology of such a presentation is `{f ∈ I : ∀ i, pderiv i f ∈ I}/I²`.

## Main results

* `KaehlerDifferential.one_tmul_D_eq_zero_iff`: the criterion for a free module of
  differentials.
* `KaehlerDifferential.one_tmul_D_eq_zero_iff_pderiv_mem`: the criterion for a polynomial
  algebra, stated for an arbitrary algebra structure whose structural map is `MvPolynomial.C`.

## Implementation notes

The polynomial statement does not assume the algebra structure on `MvPolynomial ι R` to *be*
the standard one, only that its structural map is `MvPolynomial.C`.  This is what makes it
usable on a site: the conormal sequence of a presentation by a presheaf of polynomial rings
takes its base algebra structure from `RingHom.toAlgebra` applied to the coefficient
inclusion, and that algebra structure is *not* definitionally the standard one — its scalar
multiplication is `fun r x ↦ C r * x` rather than the pointwise one, and
`MvPolynomial.C.toAlgebra = inferInstance` is not `rfl`.  The two are equal by
`Algebra.algebra_ext`, which the proof substitutes.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal
  sequence.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), whose proof reads off
  the coefficient of a variable in `d f`.
-/

@[expose] public section

open TensorProduct

universe v u

namespace KaehlerDifferential

section Basis

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] {ι : Type*}

/-- **The derivative criterion.** For a free module of relative differentials, the conormal
map of `P ⟶ P ⧸ I` kills the class of `f` exactly when every coordinate of `d f` lies in
`I`. -/
theorem one_tmul_D_eq_zero_iff (b : Module.Basis ι P (Ω[P⁄R])) (I : Ideal P) (f : P) :
    (1 : P ⧸ I) ⊗ₜ[P] KaehlerDifferential.D R P f = 0 ↔
      ∀ i, b.repr (KaehlerDifferential.D R P f) i ∈ I := by
  have hsmul : ∀ r : P, r • (1 : P ⧸ I) = Ideal.Quotient.mk I r := fun r ↦ by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one]
  rw [← (b.baseChange (P ⧸ I)).repr.map_eq_zero_iff, Finsupp.ext_iff]
  refine forall_congr' fun i ↦ ?_
  rw [Finsupp.zero_apply, Module.Basis.baseChange_repr_tmul, hsmul,
    Ideal.Quotient.eq_zero_iff_mem]

end Basis

section MvPolynomial

variable {R : Type u} [CommRing R] {ι : Type v}

/-- **The derivative criterion for a polynomial algebra.** The conormal map of
`R[ι] ⟶ R[ι] ⧸ I` kills the class of `f` exactly when every partial derivative of `f` lies in
`I`.  The algebra structure is not assumed to be the standard one, only to have
`MvPolynomial.C` as its structural map. -/
theorem one_tmul_D_eq_zero_iff_pderiv_mem [inst : Algebra R (MvPolynomial ι R)]
    (hinst : ∀ r : R, algebraMap R (MvPolynomial ι R) r = MvPolynomial.C r)
    (I : Ideal (MvPolynomial ι R)) (f : MvPolynomial ι R) :
    (1 : MvPolynomial ι R ⧸ I) ⊗ₜ[MvPolynomial ι R]
        KaehlerDifferential.D R (MvPolynomial ι R) f = 0 ↔
      ∀ i, MvPolynomial.pderiv i f ∈ I := by
  have h : inst = (by clear hinst inst; exact inferInstance) := Algebra.algebra_ext _ _ hinst
  subst h
  rw [one_tmul_D_eq_zero_iff (KaehlerDifferential.mvPolynomialBasis R ι)]
  simp only [KaehlerDifferential.mvPolynomialBasis_repr_apply]

end MvPolynomial

end KaehlerDifferential

end
