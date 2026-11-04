module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a hypersurface in a multivariate polynomial ring

Let `R` be a commutative ring, let `ι` be a type and let `P : MvPolynomial ι R`. For a commutative
`R`-algebra `K` the base change of `R[xᵢ] ⧸ (P)` along `R ⟶ K` is `K[xᵢ] ⧸ (P^φ)`, where `P^φ` is
the image of `P` under the coefficientwise map. When `K` is a field and `P^φ` is irreducible, the
latter ring is a domain, because a multivariate polynomial ring over a field is a unique
factorisation domain and so an irreducible element generates a prime ideal.

## Main results

* `MvPolynomial.isDomain_quotient_span_singleton`: the quotient of `K[xᵢ]` by an irreducible
  polynomial is a domain.
* `MvPolynomial.tensorEquivOfBaseChange`: the identification `R[xᵢ] ⊗[R] K ≃ K[xᵢ]`.
* `MvPolynomial.quotientSpanTensorEquiv`: the identification
  `(R[xᵢ] ⧸ (P)) ⊗[R] K ≃ K[xᵢ] ⧸ (P^φ)`.
* `MvPolynomial.isDomain_quotientSpan_tensor`: the base change is a domain when `P^φ` is
  irreducible.

## Implementation notes

`MvPolynomial.algebraTensorAlgEquiv` identifies `K ⊗[R] R[xᵢ]` with `K[xᵢ]` as a `K`-algebra;
the form used here has the two tensor factors in the other order and is only an `R`-algebra map,
so it is obtained from that equivalence by `Algebra.TensorProduct.comm` and
`AlgEquiv.restrictScalars`.

No finiteness hypothesis on `ι` is needed: `MvPolynomial.uniqueFactorizationMonoid` holds for an
arbitrary index type.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace MvPolynomial

/-- The quotient of a multivariate polynomial ring over a field by an irreducible polynomial is
a domain. -/
@[sga "3 III 4.6.6" "partial"]
public theorem isDomain_quotient_span_singleton {K : Type u} [Field K] {ι : Type v}
    {Q : MvPolynomial ι K} (hQ : Irreducible Q) :
    IsDomain (MvPolynomial ι K ⧸ Ideal.span {Q}) :=
  have : (Ideal.span {Q} : Ideal (MvPolynomial ι K)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hQ)
  inferInstance

variable (R : Type u) [CommRing R] (K : Type v) [CommRing K] [Algebra R K] (ι : Type w)

/-- Base change of a multivariate polynomial ring: `R[xᵢ] ⊗[R] K` is `K[xᵢ]`. -/
public noncomputable def tensorEquivOfBaseChange :
    MvPolynomial ι R ⊗[R] K ≃ₐ[R] MvPolynomial ι K :=
  (Algebra.TensorProduct.comm R (MvPolynomial ι R) K).trans
    ((algebraTensorAlgEquiv R K).restrictScalars R)

/-- `MvPolynomial.tensorEquivOfBaseChange` sends `p ⊗ₜ x` to `x` times the coefficientwise image
of `p` in `K[xᵢ]`. -/
@[simp]
public theorem tensorEquivOfBaseChange_tmul (p : MvPolynomial ι R) (x : K) :
    tensorEquivOfBaseChange R K ι (p ⊗ₜ[R] x) = x • p.map (algebraMap R K) := by
  simp [tensorEquivOfBaseChange]

/-- `MvPolynomial.tensorEquivOfBaseChange` sends the image of `p : R[xᵢ]` to the coefficientwise
image of `p` in `K[xᵢ]`. -/
@[simp]
public theorem tensorEquivOfBaseChange_algebraMap (p : MvPolynomial ι R) :
    tensorEquivOfBaseChange R K ι
        (algebraMap (MvPolynomial ι R) (MvPolynomial ι R ⊗[R] K) p) =
      p.map (algebraMap R K) := by
  rw [Algebra.TensorProduct.algebraMap_apply, tensorEquivOfBaseChange_tmul]
  simp

/-- Base change of the quotient of a multivariate polynomial ring by a principal ideal:
`(R[xᵢ] ⧸ (P)) ⊗[R] K` is `K[xᵢ] ⧸ (P^φ)`. -/
public noncomputable def quotientSpanTensorEquiv (P : MvPolynomial ι R) :
    (MvPolynomial ι R ⧸ Ideal.span {P}) ⊗[R] K ≃ₐ[R]
      MvPolynomial ι K ⧸ Ideal.span {P.map (algebraMap R K)} :=
  (Algebra.TensorProduct.quotientTensorEquiv (R := R) R K (MvPolynomial ι R)
      (Ideal.span {P})).trans
    (Ideal.quotientEquivAlg _ _ (tensorEquivOfBaseChange R K ι) (by
      rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
      simp))

/-- If the coefficientwise image of `P` in `K[xᵢ]` is irreducible, where `K` is a field, then the
base change `(R[xᵢ] ⧸ (P)) ⊗[R] K` is a domain. -/
public theorem isDomain_quotientSpan_tensor {K : Type v} [Field K] [Algebra R K]
    (P : MvPolynomial ι R) (hP : Irreducible (P.map (algebraMap R K))) :
    IsDomain ((MvPolynomial ι R ⧸ Ideal.span {P}) ⊗[R] K) :=
  have := isDomain_quotient_span_singleton hP
  MulEquiv.isDomain _ (quotientSpanTensorEquiv R K ι P).toRingEquiv.toMulEquiv

end MvPolynomial

end
