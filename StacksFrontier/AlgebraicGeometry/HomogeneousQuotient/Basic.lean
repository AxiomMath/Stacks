module

public import StacksFrontier.AlgebraicGeometry.HomogeneousQuotient.Defs
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-!
# The quotient map of a homogeneous ideal as a graded ring homomorphism

Let `A` be a graded ring and `I` a homogeneous ideal, with `A ⧸ I` carrying the grading
`quotientGrading 𝒜 I`. The quotient map `A → A ⧸ I` is a graded ring homomorphism
`𝒜 →+*ᵍ quotientGrading 𝒜 I`; it is surjective in every degree, its kernel is `I`, and it
commutes with taking graded components. For `ℕ`-graded `A`, `projQuotient` is the scheme
`Proj (A ⧸ I)`.

## Main definitions

* `Stacks.RingTheory.HomogeneousQuotient.quotientMk`: the quotient map as a bundled graded ring
  homomorphism `𝒜 →+*ᵍ quotientGrading 𝒜 I`.
* `Stacks.RingTheory.HomogeneousQuotient.projQuotient`: `Proj` of a quotient of a graded ring by
  a homogeneous ideal, as a scheme.

## Main results

* `Stacks.RingTheory.HomogeneousQuotient.surjective_gradedAddHom_quotientMk`: the quotient map
  is surjective in every degree.
* `Stacks.RingTheory.HomogeneousQuotient.ker_quotientMk`: its kernel is `I`.
* `Stacks.RingTheory.HomogeneousQuotient.coe_decompose_quotientGrading_mk`: the degree-`i`
  component of the class of `a` is the class of the degree-`i` component of `a`.
* `Stacks.RingTheory.HomogeneousQuotient.toIdeal_comap_quotientMk` and
  `Stacks.RingTheory.HomogeneousQuotient.toIdeal_map_quotientMk`: transporting homogeneous
  ideals along the quotient map agrees with transporting the underlying ideals.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
-/

@[expose] public noncomputable section

open DirectSum

universe u v w

namespace Stacks.RingTheory.HomogeneousQuotient

variable {ι : Type v} {R : Type u} {A : Type w} [DecidableEq ι] [AddMonoid ι]
  [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (I : HomogeneousIdeal 𝒜)

/-- The quotient map `A → A ⧸ I`, for `I` a homogeneous ideal, as a graded ring homomorphism
`𝒜 →+*ᵍ quotientGrading 𝒜 I`. -/
def quotientMk : 𝒜 →+*ᵍ quotientGrading 𝒜 I where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem h := quotientGrading_mk_mem 𝒜 I h

/-- The graded quotient map sends `a` to its class `Ideal.Quotient.mk I.toIdeal a`. -/
@[simp]
theorem quotientMk_apply (a : A) : quotientMk 𝒜 I a = Ideal.Quotient.mk I.toIdeal a := rfl

/-- The degree-`i` component of the class of `a` is the class of the degree-`i` component
of `a`. -/
theorem coe_decompose_quotientGrading_mk (a : A) (i : ι) :
    ((DirectSum.decompose (quotientGrading 𝒜 I) (Ideal.Quotient.mk I.toIdeal a) i :
        quotientGrading 𝒜 I i) : A ⧸ I.toIdeal)
      = Ideal.Quotient.mk I.toIdeal ((DirectSum.decompose 𝒜 a i : A)) :=
  (GradedRingHom.map_directSumDecompose (f := quotientMk 𝒜 I)).symm

/-- The quotient map is surjective in every degree: the degree-`i` piece of `A ⧸ I` is by
construction the image of `𝒜 i`. -/
theorem surjective_gradedAddHom_quotientMk (i : ι) :
    Function.Surjective (GradedRingHom.gradedAddHom (quotientMk 𝒜 I) i) := by
  intro y
  obtain ⟨a, ha, hay⟩ := (mem_quotientGrading_iff 𝒜 I).1 y.2
  exact ⟨⟨a, ha⟩, Subtype.ext hay⟩

/-- The kernel of the graded quotient map is the ideal one quotiented by. -/
theorem ker_quotientMk : RingHom.ker (quotientMk 𝒜 I) = I.toIdeal := Ideal.mk_ker

/-- Pulling a homogeneous ideal of `A ⧸ I` back along the graded quotient map is, on underlying
ideals, the ordinary `Ideal.comap`. -/
theorem toIdeal_comap_quotientMk (J : HomogeneousIdeal (quotientGrading 𝒜 I)) :
    (J.comap (quotientMk 𝒜 I)).toIdeal = J.toIdeal.comap (Ideal.Quotient.mk I.toIdeal) := rfl

/-- Pushing a homogeneous ideal of `A` forward along the graded quotient map is, on underlying
ideals, the ordinary `Ideal.map`. -/
theorem toIdeal_map_quotientMk (J : HomogeneousIdeal 𝒜) :
    (J.map (quotientMk 𝒜 I)).toIdeal = J.toIdeal.map (Ideal.Quotient.mk I.toIdeal) := rfl

/-- **`Proj` of a quotient by a homogeneous ideal.** For an `ℕ`-graded commutative ring `A` and
a homogeneous ideal `I`, the scheme `Proj (A ⧸ I)`, where `A ⧸ I` carries the grading
`quotientGrading 𝒜 I`. -/
def projQuotient {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜) :
    AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (quotientGrading 𝒜 I)

end Stacks.RingTheory.HomogeneousQuotient

end
