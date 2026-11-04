module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Rescaling the variables of a homogeneous polynomial

Evaluating a homogeneous polynomial of degree `n` at `u * v k` instead of at `v k` multiplies the
value by `uⁿ`. This is the degree-one-generation step of the uniqueness clause of
[Stacks, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8): it is what upgrades an identity
between two ring homomorphisms out of `R[T₀, …, Tₙ]` *on the variables* to an identity on every
homogeneous element, which is the form
`AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit` consumes.

`MvPolynomial.IsHomogeneous.eval₂` and `MvPolynomial.IsHomogeneous.aeval` are different statements:
they say that the *value* of a homogeneous polynomial at homogeneous arguments is again
homogeneous. Neither relates the values at two different families of arguments.

## Main results

* `MvPolynomial.IsHomogeneous.eval₂_const_mul`: `eval₂ g (u * v ·) φ = uⁿ * eval₂ g v φ` for `φ`
  homogeneous of degree `n`.
* `MvPolynomial.IsHomogeneous.eval₂Hom_const_mul`: the same for `MvPolynomial.eval₂Hom`.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public section

namespace MvPolynomial.IsHomogeneous

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- **Evaluating a homogeneous polynomial of degree `n` at `u · vₖ` multiplies the value by
`uⁿ`.** Each monomial of `φ` has total degree `n`, so it contributes exactly `n` factors of `u`.
-/
theorem eval₂_const_mul {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n) (g : R →+* S)
    (v : σ → S) (u : S) :
    MvPolynomial.eval₂ g (fun k => u * v k) φ = u ^ n * MvPolynomial.eval₂ g v φ := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hφ.degree_eq_sum_deg_support hd, ← Finset.prod_pow_eq_pow_sum]
  simp only [mul_pow, Finset.prod_mul_distrib]
  ring

/-- `eval₂_const_mul` for the ring homomorphism `MvPolynomial.eval₂Hom`. -/
theorem eval₂Hom_const_mul {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n) (g : R →+* S)
    (v : σ → S) (u : S) :
    MvPolynomial.eval₂Hom g (fun k => u * v k) φ = u ^ n * MvPolynomial.eval₂Hom g v φ :=
  hφ.eval₂_const_mul g v u

end MvPolynomial.IsHomogeneous

end
