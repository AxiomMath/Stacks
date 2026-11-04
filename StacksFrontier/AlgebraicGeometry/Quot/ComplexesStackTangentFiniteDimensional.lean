module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackTangentSpaceProved
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeAtlasSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-!
# Stacks 0DLL: the tangent space and infinitesimal automorphisms of `Complexes_{X/B}`

In Situation 0DLE, with `S` locally Noetherian and `B ⟶ S` locally of finite presentation, the
predeformation category `𝓕_{𝒳,k,x₀}` of `𝒳 = Complexes_{X/B}` at an object `x₀` over a field
`k` of finite type over `S` has a finite dimensional tangent space and finite dimensional
infinitesimal automorphisms
(`finiteDimensional_tangentSpace_infinitesimalAutomorphisms_complexes` in
`AlgebraicGeometry.Space.ComplexesSituation`).

The hypotheses are those of the source: `Y ⟶ S` is locally of finite presentation, and `k` is
presented as in Stacks Section 07T2, with `Λ → k` finite and `Spec Λ ⟶ S` an open immersion.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin Deformation.ComplexLift

universe u

/-- A finite algebra `k` over `Λ`, mapped to `S` through an open immersion `Spec Λ ⟶ S`, is
locally of finite type over `S`. -/
theorem AlgebraicGeometry.locallyOfFiniteType_specMap_comp_of_isOpenImmersion
    {Λ k : Type u} [CommRing Λ] [CommRing k] [Algebra Λ k] [Module.Finite Λ k]
    {S : AlgebraicGeometry.Scheme.{u}} (iΛ : AlgebraicGeometry.Spec (.of Λ) ⟶ S)
    (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ) :
    AlgebraicGeometry.LocallyOfFiniteType
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := by
  have : AlgebraicGeometry.LocallyOfFiniteType
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Λ k))) := by
    rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_finite (RingHom.finite_algebraMap.mpr inferInstance)
  infer_instance

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/- The instances under which `finiteDimensional_tangentSpaceModuleOfSatisfiesRS_proved` is stated.
`AlgebraicGeometry.Space.instModulesHasDerivedCategory` is the model of the derived category of
modules on an algebraic space at which `AlgebraicGeometry.Space.derivedModules` is formed. -/
attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

attribute [local instance] complexesCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

/-- In Situation 0DLE (`f : X ⟶ Y` proper, flat and of finite presentation, the `B` of the source
being `Y`), assume that `S` is locally Noetherian and `Y ⟶ S` is locally of finite presentation.
Let `k` be a field of finite type over `S`, presented as in Stacks Section 07T2 through an affine
open `Spec Λ ⊆ S` with `Λ → k` finite, and let `x₀` be an object of `𝒳 = Complexes_{X/Y}` over
`Spec k`. Then `𝒳` satisfies (RS), so that the predeformation category `𝓕_{𝒳,k,x₀}` is a
deformation category and the spaces of Stacks Section 07WY are defined, and the tangent space
`T𝓕_{𝒳,k,x₀}` (`Deformation.Artin.tangentSpaceModuleOfSatisfiesRS`) and the infinitesimal
automorphisms `Inf(𝓕_{𝒳,k,x₀})` (`Deformation.Artin.infinitesimalAutomorphismModuleOfSatisfiesRS`,
at every object over `k` and every choice of pushforwards) are finite dimensional over `k`. -/
@[stacks 0DLL]
theorem finiteDimensional_tangentSpace_infinitesimalAutomorphisms_complexes
    (D : ComplexesSituation B S hS) [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.obj))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    SatisfiesRS B S hS (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D) ∧
      ∀ hRS : SatisfiesRS B S hS (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D),
        FiniteDimensional k (tangentSpaceModuleOfSatisfiesRS B S hS (complexesFunctor D)
            (complexesFunctor_isFiberedInGroupoids D) hRS iΛ x₀ hx₀
            (locallyOfFiniteType_specMap_comp_of_isOpenImmersion iΛ hiΛ)
            (quasiCompact_of_spec_field _)) ∧
          ∀ x P, FiniteDimensional k (infinitesimalAutomorphismModuleOfSatisfiesRS B S hS
            (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D) hRS iΛ x₀ hx₀
            (locallyOfFiniteType_specMap_comp_of_isOpenImmersion iΛ hiΛ)
            (quasiCompact_of_spec_field _) x P) :=
  ⟨satisfiesRS_complexesFunctor_proved D, fun _ =>
    finiteDimensional_tangentSpaceModuleOfSatisfiesRS_proved D
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hY) iΛ hiΛ x₀ hx₀
      (locallyOfFiniteType_specMap_comp_of_isOpenImmersion iΛ hiΛ)
      (quasiCompact_of_spec_field _)⟩

end AlgebraicGeometry.Space.ComplexesSituation

end
