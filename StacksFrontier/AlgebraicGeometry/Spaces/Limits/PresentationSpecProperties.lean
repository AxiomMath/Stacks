module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PresentationStageDescent

/-!
# The spectrum of a standard-étale presentation

Let `A` be a commutative ring and `g₁, …, gₙ` polynomials in `n` variables over `A` whose
Jacobian determinant is invertible in `C = A[x₁, …, xₙ] ⧸ (g₁, …, gₙ)`. Then `C` is an étale
`A`-algebra, by the recognition half of Stacks 00U9
(`Algebra.etale_mvPolynomialQuotient_of_isUnit_det`), hence flat over `A`; and the morphism
`Spec C ⟶ Spec A` is therefore flat as a morphism of schemes. Its surjectivity, on the other
hand, is not automatic and is read off surjectivity of the comparison of prime spectra.

Both are the properties the concluding step of the proof of Stacks 07SQ asks of
`Spec B_i ⟶ Spec A_i`, where `B_i` is the presentation descended to a stage.

## Main results

* `AlgebraicGeometry.Space.module_flat_presentationAlgebra`: a standard-étale presentation is
  flat over the base ring.
* `AlgebraicGeometry.Space.flat_Spec_map_presentationStructureHom`: the spectrum of a
  standard-étale presentation is flat over the spectrum of the base ring.
* `AlgebraicGeometry.Space.surjective_Spec_map_presentationStructureHom`: it is surjective as
  soon as the comparison of prime spectra is.

## Implementation notes

The structure homomorphism of a presentation,
`AlgebraicGeometry.Space.presentationStructureHom`, is the algebra map of the quotient algebra,
which is `AlgebraicGeometry.Space.algebraMap_eq_presentationStructureHom`; both statements below
pass through that identification, flatness through `RingHom.flat_algebraMap_iff` and
surjectivity because the underlying map of `Spec` of a ring homomorphism is the comap on prime
spectra.

Flatness of the morphism of schemes is obtained from flatness of the ring map by
`AlgebraicGeometry.HasRingHomProperty.Spec_iff`, flatness of morphisms of schemes being a
ring-homomorphism property.

## References

* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MvPolynomial

universe u

namespace AlgebraicGeometry.Space

variable {A : Type u} [CommRing A] {n : ℕ} (g : Fin n → MvPolynomial (Fin n) A)

/-- **A standard-étale presentation is flat over the base ring.** Invertibility of the Jacobian
determinant makes the quotient an étale algebra, by the recognition half of Stacks 00U9, and an
étale algebra is flat. -/
theorem module_flat_presentationAlgebra
    (hΔ : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g))) :
    Module.Flat A (presentationAlgebra g) := by
  have := Algebra.etale_mvPolynomialQuotient_of_isUnit_det g hΔ
  infer_instance

/-- **The spectrum of a standard-étale presentation is flat over the spectrum of the base
ring.** -/
theorem flat_Spec_map_presentationStructureHom
    (hΔ : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g))) :
    AlgebraicGeometry.Flat
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g))) := by
  rw [← algebraMap_eq_presentationStructureHom g]
  exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat.{u})).mpr
    (RingHom.flat_algebraMap_iff.mpr (module_flat_presentationAlgebra g hΔ))

/-- **The spectrum of a standard-étale presentation is surjective over the spectrum of the base
ring** as soon as the comparison of prime spectra is surjective: the underlying map of the
spectrum of a ring homomorphism is that comparison. -/
theorem surjective_Spec_map_presentationStructureHom
    (hsurj : Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (presentationAlgebra g)))) :
    AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g))) := by
  rw [← algebraMap_eq_presentationStructureHom g]
  exact ⟨hsurj⟩

end AlgebraicGeometry.Space

end
