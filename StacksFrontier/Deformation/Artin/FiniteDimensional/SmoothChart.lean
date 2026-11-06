module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.InfChart

/-!
# Finite-dimensionality at a point of a category with a smooth chart

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S` satisfying (RS), with a smooth surjective chart `f : (Sch/V) ⟶ 𝒳` by a scheme `V` locally of
finite type over `S`. Then for every field `k` of finite type over `S` and every object `x₀` of
`𝒳` over `Spec k`, the predeformation category `𝓕_{𝒳,k,x₀}` is a deformation category whose tangent
space and space of infinitesimal automorphisms are finite-dimensional over `k`. Every algebraic
stack satisfies (RS), and the statement is stated here for any `𝒳` satisfying (RS), so that it
applies also to `(Sch/V) ×_𝒳 (Sch/V)`.

## Main results

* `Deformation.Artin.isFiniteDimensionalDeformationCategory_of_smoothChart`: the predeformation
  category of `𝒳` at `x₀` is a deformation category with finite-dimensional tangent space and
  finite-dimensional infinitesimal automorphisms.

## References

* [Stacks, Tag 07X1](https://stacks.math.columbia.edu/tag/07X1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Artin

attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If `𝒳` satisfies (RS) and has a smooth surjective chart `f` by a scheme `V` locally of finite
type over `S`, then for every field `k` finite over `Λ` and every object `x₀` of `𝒳` over
`Spec k`, the predeformation category of `𝒳` at `x₀` is a deformation category whose tangent
space and infinitesimal automorphisms are finite-dimensional over `k`. -/
theorem isFiniteDimensionalDeformationCategory_of_smoothChart [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (V : BigFppfOver B S hS) [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (f : Stack.schemeFibredCategory B S hS V ⟶ 𝒳)
    (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hprop : ∀ (W : BigFppfOver B S hS)
      (yv : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.obj)
      (_hyv : yv ⋙ 𝒳.val.p = Over.map W.hom)
      (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B W.left.1 W.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map W.hom) (Stack.schemeFibredCategory B S hS V).val.p
          𝒳.val.p yv (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS W
        ((spacesOverSmallerBaseFunctor B W.left.1 S W.left.2 hS W.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ) (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
    IsFiniteDimensionalDeformationCategory
      (predeformationCategory iΛ (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection := by
  have : IsOpenImmersion iΛ := hiΛ
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  let q := 𝒳.val.p ⋙ Over.post B.inclusion
  let D₀ := predeformationCategory iΛ q x₀ hx₀
  let := D₀.category
  have hD₀ := isDeformationCategory_predeformationCategory B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids
    hRS iΛ x₀ hx₀ hfinite.1 hfinite.2
  refine ⟨hD₀, ?_, ?_⟩
  · exact finiteDimensional_tangentSpaceArtinian_of_tangentModuleAt hD₀
      ((finiteDimensional_tangentModuleAt_uLift_iff hD₀).mpr
        (finiteDimensional_tangentModuleAt_of_smoothChart 𝒳 hRS V f hf hprop iΛ hiΛ x₀ hx₀
          hfinite))
  intro x hx PF
  refine finiteDimensional_infinitesimalAutomorphismLinearLift_of_localized hD₀.satisfiesRS PF ?_
  obtain ⟨l, _, _, _, _, hkl, u₀, hu₀, hxₗ, η, hηbase⟩ :=
    exists_finite_extension_chart_point 𝒳 V f hf hprop iΛ x₀ hx₀
  have := hkl
  have : Module.Finite Λ l := Module.Finite.trans k l
  let T : ChangeOfFieldsSituation.{u, u, u} := { Λ := Λ, k := k, l := l }
  have hfinl := locallyOfFiniteType_quasiCompact_of_finite (k := k) (l := l) iΛ hfinite
  let Dₗ := predeformationCategory iΛ q ((CatFiberedInGroupoids.homFunctor f).obj u₀) hxₗ
  let := Dₗ.category
  have hDₗ := isDeformationCategory_predeformationCategory B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids
    hRS iΛ ((CatFiberedInGroupoids.homFunctor f).obj u₀) hxₗ hfinl.1 hfinl.2
  have hcart : 𝒳.val.p.IsCartesian (𝒳.val.p.map η) η := by
    have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝒳.val.p.map η) η
    infer_instance
  let C := Site.changeOfFieldFunctor T iΛ B hS 𝒳.val.p x₀ _ hx₀ hxₗ η 𝒳.isFiberedInGroupoids
    hcart hηbase
  let F := C.toFunctor
  have hFcomm := C.projection_comm
  have : F.Faithful := (Site.changeOfFieldFunctor_isEquivalence T iΛ B hS 𝒳.val.p x₀ _
    hx₀ hxₗ η 𝒳.isFiberedInGroupoids hcart hηbase hfinite hRS).faithful
  have hG : IsDeformationCategory (changeOfFieldsProjection.{u, u, u, u} T D₀.projection) :=
    ⟨changeOfFieldsProjection_isPredeformationCategory T D₀.projection hD₀.predeformation,
      changeOfFieldsProjection_satisfiesRS T D₀.projection hD₀.satisfiesRS⟩
  let xₗ' : (changeOfFieldsProjection T D₀.projection).Fiber (residueFieldObject T.Λ T.l) :=
    (Classical.choice hG.predeformation.specialFiber).inverse.obj ⟨PUnit.unit⟩
  let Q := chosenPushforwardsAtOfCofiberedInGroupoids hG.predeformation.cofibered xₗ'.1
  let Q' := chosenPushforwardsAtOfCofiberedInGroupoids hDₗ.predeformation.cofibered (F.obj xₗ'.1)
  obtain ⟨y, hy, Py, hPy⟩ :=
    exists_finiteDimensional_localized_of_smoothChart 𝒳 hRS V f hf hprop iΛ hiΛ u₀ hu₀ hxₗ hfinl
  have hFx : Dₗ.projection.obj (F.obj xₗ'.1) = residueFieldObject Λ l :=
    (Functor.congr_obj hFcomm xₗ'.1).trans xₗ'.2
  obtain ⟨j, -⟩ := existsUnique_pointIso hDₗ.predeformation ⟨F.obj xₗ'.1, hFx⟩ ⟨y, hy⟩
  have hQ := finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful F hFcomm
    hG.satisfiesRS hDₗ.satisfiesRS Q Q'
    (finiteDimensional_localizedAutomorphismFunctorTangent_of_hom hDₗ.satisfiesRS j.hom.1 hy Q'
      Py hPy)
  exact finiteDimensional_localizedAutomorphismFunctorTangent_of_changeOfFields T D₀.projection hD₀
    ⟨x, hx⟩ PF xₗ' Q hQ

end Deformation.Artin
