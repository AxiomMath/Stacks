module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatPredeformationFiniteTangentExt
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatPredeformationFiniteTangentInjective
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# The tangent space of a point of `Spaces'_{fp, flat, proper}` over any base is finite

Let `S` be any scheme, `𝒳 = Spaces'_{fp, flat, proper}` the stack of finitely presented, flat and
proper algebraic spaces over the big fppf site of `S`, and `x₀ = (X₀ ⟶ Spec k)` an object of `𝒳`
over the spectrum of a field, with `Spec k ⟶ S` presented through `Spec k ⟶ Spec Λ ⟶ S`. If the
predeformation category `𝓕_{𝒳,k,x₀}` over `𝒞_Λ` (Stacks 07T2) is a deformation category, its
tangent space `T𝓕_{𝒳,k,x₀}` is a finite-dimensional `k`-vector space.

This is the tangent-space part of the argument of the proof of Stacks 0D1K, carried out over an
arbitrary base (the statement registered for Stacks 0D1K is over `Spec ℤ`,
`AlgebraicGeometry.ProperFlatSpaceDeformation.finiteDimensional_predeformationCategory`). A
deformation of `x₀` over `k[V]` has a class in `Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)`, the class
(Stacks 0GQ5) of the extension of `f₀⁻¹𝒪_{Spec k}`-algebras given by its structure sheaf
(Stacks 0D17); the classes are natural in `V`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtClassAt_naturality`), injective at
`V = k` (`AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtClassAt_injective`: Stacks 05YZ,
05Z1), so linear for the vector-space structure of Stacks 06IH, and
`Ext¹(NL_{X₀/k}, 𝒪_{X₀})` is finite dimensional because `X₀` is proper over `k`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.finiteDimensional_tangentExtFunctor_obj`:
Stacks 0D0Z, 0D0T).

## Main results

* `ProperFlatSpaceDeformation.finiteDimensional_tangentSpaceArtinian_predeformation`:
  the tangent space of `𝓕_{𝒳,k,x₀}` is finite dimensional.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

universe u

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CartesianProperFlatSpaces B S hS)
  (hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

attribute [local instance] PredeformationConstruction.category in
/-- **The tangent space of `𝓕_{𝒳,k,x₀}` is finite dimensional, over any base.** Let `S` be a
scheme, `x₀ = (X₀ ⟶ Spec k)` an object of `𝒳 = Spaces'_{fp, flat, proper}` over the spectrum of a
field, with `Spec k ⟶ S` presented through `Spec k ⟶ Spec Λ ⟶ S`. Whenever the predeformation
category `𝓕_{𝒳,k,x₀}` over `𝒞_Λ` is a deformation category, its tangent space (with the
vector-space structure of Stacks 06IH) is a finite-dimensional `k`-vector space.

This is the tangent-space part of the argument of Stacks 0D1K over a general base: the
tangent space embeds `k`-linearly in `Ext¹(NL_{X₀/k}, 𝒪_{X₀})`, which is finite dimensional
because `X₀` is proper over `k`. -/
theorem finiteDimensional_tangentSpaceArtinian_predeformation :
    letI := (predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion) x₀ hx₀).category
    ∀ hD : IsDeformationCategory (predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙
        Over.post B.inclusion) x₀ hx₀).projection,
      letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor (predeformationCategory iΛ
          (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
            hx₀).projection).p) := ⟨hD.predeformation⟩
      letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
          (BasedCategory.ofFunctor (predeformationCategory iΛ
            (cartesianProperFlatProjection B S hS ⋙
            Over.post B.inclusion) x₀ hx₀).projection) hD.predeformation.cofibered))) :=
        ⟨tangentConditionS2 hD⟩
      FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
        (BasedCategory.ofFunctor (predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙
          Over.post B.inclusion) x₀ hx₀).projection) hD.predeformation.cofibered)) := by
  intro hD
  have := finiteDimensional_tangentExtFunctor_obj B S hS iΛ x₀ hx₀
  exact finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace _ hD.predeformation
    (tangentConditionS2 hD)
    (finiteDimensional_artinianTangentSpace_of_natural_injection
      (predeformationBased B S hS iΛ x₀ hx₀) hD.predeformation (tangentConditionS2 hD)
      (tangentExtFunctor B S hS iΛ x₀ hx₀)
      (tangentExtClassAt B S hS iΛ x₀ hx₀ hD.predeformation.cofibered)
      (fun f z => tangentExtClassAt_naturality B S hS iΛ x₀ hx₀ hD.predeformation.cofibered f z)
      (tangentExtClassAt_injective B S hS iΛ hD.predeformation.cofibered))

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
