module

public import StacksFrontier.AlgebraicGeometry.HomogeneousQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualSurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Proj` of a homogeneous quotient is a closed subscheme of `Proj`

For an `ℕ`-graded commutative algebra `A` and a homogeneous ideal `I`, the canonical morphism
`Proj (A ⧸ I) ⟶ Proj A` induced by the graded quotient map is a closed immersion.

## Main results

* `Stacks.RingTheory.HomogeneousQuotient.isClosedImmersion_projMapData_quotientMk`: the
  canonical morphism from `Proj` of a homogeneous quotient to `Proj` of the ambient graded ring
  is a closed immersion.

## References

* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.RelativeProjChain

universe u v

namespace Stacks.RingTheory.HomogeneousQuotient

/-- For an `ℕ`-graded commutative `R`-algebra `A` and a homogeneous ideal `I`, the canonical
morphism `Proj (A ⧸ I) ⟶ Proj A` induced by the graded quotient map `quotientMk` is a closed
immersion. -/
@[ega "II 2.9.2" "(i), special case", ega "II 3.6.2" "(i), special case"]
theorem isClosedImmersion_projMapData_quotientMk {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) :
    IsClosedImmersion
      (ProjTwistCompare.projMapData 𝒜 (quotientGrading 𝒜 I) (quotientMk 𝒜 I)).hom :=
  isClosedImmersion_projMapData_hom_of_eventually_surjective 𝒜 (quotientGrading 𝒜 I)
    (quotientMk 𝒜 I) (Filter.Eventually.of_forall (surjective_gradedAddHom_quotientMk 𝒜 I))

end Stacks.RingTheory.HomogeneousQuotient

end
