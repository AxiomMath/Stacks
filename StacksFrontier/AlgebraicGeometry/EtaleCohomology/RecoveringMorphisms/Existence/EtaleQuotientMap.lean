module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of a presented étale algebra

If `R[x₁, …, xₙ]/(P₁, …, Pₘ)` is étale over `R`, then for any ring map `f : R ⟶ A` the
algebra `A[x₁, …, xₙ]/(f(P₁), …, f(Pₘ))` is étale over `A`: it is the base change.

This is the form in which étaleness reaches the stalks in the existence half of Stacks 04I7: a
standard presentation of an étale chart over an affine open of the target is pushed to the
stalk ring of the target at a point, where Stacks 04GX needs the presented algebra to be étale.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
-/

@[expose] public section

open TensorProduct

namespace MvPolynomial

variable {R A : Type*} [CommRing R] [CommRing A] {σ ι : Type*}

/-- **Étaleness of a presented algebra is stable under base change of the coefficients.** -/
theorem etale_quotient_map (f : R →+* A) (P : ι → MvPolynomial σ R)
    [Algebra.Etale R (MvPolynomial σ R ⧸ Ideal.span (Set.range P))] :
    Algebra.Etale A (MvPolynomial σ A ⧸ Ideal.span (Set.range (fun i => map f (P i)))) := by
  let := f.toAlgebra
  let I := Ideal.span (Set.range P)
  let e₁ := Algebra.TensorProduct.tensorQuotientEquiv (R := R) A (MvPolynomial σ R) A I
  let e₂ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) R A
  have hI : (I.map (Algebra.TensorProduct.includeRight (A := A) (R := R))).map
      (e₂ : A ⊗[R] MvPolynomial σ R →+* MvPolynomial σ A) =
      Ideal.span (Set.range (fun i => map f (P i))) := by
    rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    congr 1
    ext i
    simp [e₂, MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]
  exact Algebra.Etale.of_equiv (e₁.trans (Ideal.quotientEquivAlg _ _ e₂ hI.symm))

end MvPolynomial
