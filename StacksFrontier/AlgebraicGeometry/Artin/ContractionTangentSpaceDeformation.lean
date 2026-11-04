module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionTangentSpace
public import StacksFrontier.Deformation.Artin.FunctorDeformationCategory

/-!
# The tangent spaces of Artin's contraction functor (Stacks 0GI7)

In Situation 0GH8, let `F` be the functor of Stacks 0GHA. For every field `k` of finite type over
`S` and every `x₀ ∈ F(Spec k)`, the predeformation category `𝓕_{F,k,x₀}` is a deformation category,
because `F` satisfies (RS) (Stacks 0GI6) and the predeformation categories of a functor satisfying
(RS) are deformation categories (Stacks 07WU). So `𝓕_{F,k,x₀}` is a predeformation category whose
functor of isomorphism classes satisfies (S2) (Stacks 07WV), its tangent space carries the
vector-space structure of Stacks 06IH, and that vector space is finite dimensional: this is
Stacks 0GI7, the finite-dimensionality being
`AlgebraicGeometry.Artin.ContractionSituation.hasFiniteDimensionalTangentSpaces`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isDeformationCategory_predeformationCategory`:
  the predeformation categories of `F` are deformation categories.
* `AlgebraicGeometry.Artin.ContractionSituation.finiteDimensional_artinianTangentSpace`:
  **Stacks 0GI7**.

## References

* [Stacks Project, Tag 0GI7](https://stacks.math.columbia.edu/tag/0GI7)
* [Stacks Project, Tag 0GI6](https://stacks.math.columbia.edu/tag/0GI6)
* [Stacks Project, Tag 07WU](https://stacks.math.columbia.edu/tag/07WU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

open Deformation Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)

/-- **The predeformation categories of Artin's contraction functor are deformation categories.**
For a field `k` of finite type over `S`, an affine open `Spec Λ ⊆ S` through which `Spec k ⟶ S`
factors with `Λ → k` finite, and `x₀ ∈ F(Spec k)`, the category `𝓕_{F,k,x₀}` is a deformation
category over `𝒞_Λ`, since `F` satisfies (RS) (Stacks 0GI6). -/
theorem isDeformationCategory_predeformationCategory
    (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ) (x₀ : (contractionFunctor c).Elementsᵒᵖ)
    (hx₀ : (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := (predeformationCategory iΛ
      (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) x₀ hx₀).category
    IsDeformationCategory (BasedCategory.ofFunctor (predeformationCategory iΛ
      (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) x₀ hx₀).projection).p :=
  LocallyNoetherianOver.isDeformationCategory_predeformationCategory_of_satisfiesRS
    (contractionFunctor_satisfiesRS c) iΛ x₀ hx₀
    (LocallyNoetherianOver.locallyOfFiniteType_quasiCompact_of_isOpenImmersion iΛ hiΛ).1
    (LocallyNoetherianOver.locallyOfFiniteType_quasiCompact_of_isOpenImmersion iΛ hiΛ).2

/-- **Stacks 0GI7.** In Situation 0GH8 the tangent spaces of the functor `F` of Stacks 0GHA are
finite dimensional: for every field `k` of finite type over `S`, every affine open
`Spec Λ ⊆ S` through which `Spec k ⟶ S` factors with `Λ → k` finite, and every
`x₀ ∈ F(Spec k)`, the predeformation category `𝓕_{F,k,x₀}` is a deformation category (so a
predeformation category whose functor of isomorphism classes satisfies (S2)), and its tangent
space, with the vector-space structure of Stacks 06IH these give it, is a finite dimensional
`k`-vector space. -/
@[stacks 0GI7]
theorem finiteDimensional_artinianTangentSpace
    (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ) (x₀ : (contractionFunctor c).Elementsᵒᵖ)
    (hx₀ : (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let D := predeformationCategory iΛ
      (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) x₀ hx₀
    letI : Category D.carrier := D.category
    let hD := isDeformationCategory_predeformationCategory c Λ k iΛ hiΛ x₀ hx₀
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D.projection).p) :=
      ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
        (isomorphismClasses (BasedCategory.ofFunctor D.projection) hD.predeformation.cofibered))) :=
      ⟨tangentConditionS2 hD⟩
    FiniteDimensional k (artinianTangentSpace Λ k
      (isomorphismClasses (BasedCategory.ofFunctor D.projection) hD.predeformation.cofibered)) :=
  hasFiniteDimensionalTangentSpaces c Λ k iΛ hiΛ x₀ hx₀
    (isDeformationCategory_predeformationCategory c Λ k iΛ hiΛ x₀ hx₀).predeformation
    (tangentConditionS2 (isDeformationCategory_predeformationCategory c Λ k iΛ hiΛ x₀ hx₀))

end AlgebraicGeometry.Artin.ContractionSituation

end
