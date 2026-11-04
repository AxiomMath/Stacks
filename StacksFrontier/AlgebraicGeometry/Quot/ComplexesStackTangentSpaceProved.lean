module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackPushoutsProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityFibreFinite
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreTrivialAutNatural
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFlatPushoutProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackTangentSpaceBase

/-!
# Stacks 0DLL for `Complexes_{X/B}`

In Situation 0DLE, let `S` be locally Noetherian and `B ⟶ S` locally of finite type. For a
field `k` of finite type over `S` and an object `x₀ = (Spec k, g₀, E₀)` of
`𝒳 = Complexes_{X/B}` over `Spec k`, the tangent space `T𝓕_{𝒳,k,x₀}` and the infinitesimal
automorphisms `Inf(𝓕_{𝒳,k,x₀})` of Artin's Axioms, Section 07WY, are finite dimensional.

## Main results

* `satisfiesRSStar_complexesFunctor_proved`: condition (RS*) for `Complexes_{X/B}`.
* `finiteDimensional_tangentSpaceModuleOfSatisfiesRS_proved`: Stacks 0DLL.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin Deformation.ComplexLift

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

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

variable (D : ComplexesSituation B S hS)

/-- **Condition (RS*) for `Complexes_{X/B}`**: in Situation 0DLE, the structure functor
`complexesFunctor D` of `Complexes_{X/B}` satisfies condition (RS*). -/
theorem satisfiesRSStar_complexesFunctor_proved :
    SatisfiesRSStar B S hS (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D) :=
  satisfiesRSStar_complexesFunctor D (complexesFunctor_isFiberedInGroupoids D)
    (complexes_hasRepresentableDiagonal_proved D)
    (isPushout_of_isFlat_of_isPushout_schemeSpace B S hS)
    (exists_glue_of_isPushout_of_derivedPushoutEssentialImage B S hS
      (derivedPushoutEssentialImage.{u + 1, u + 1, u + 1, u + 1, u} B S hS))
    (fun h hfin E' E e hE => D.isRelativelyPerfect_of_isFiniteOrderThickening_proved h hfin E' E
      e hE)

section TangentSpace

/- The fibre steps elaborate `HasDerivedCategory.standard` on the coefficient rings of the
small étale site; the generic sheafification instances make each such query slow. -/
attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

/-- **Stacks 0DLL.** In Situation 0DLE, let `S` be locally Noetherian and `Y ⟶ S` locally of
finite type (the source assumes `B ⟶ S` locally of finite presentation). Let `k` be a field of
finite type over `S`, through an affine open `Spec Λ ⊆ S` with `Λ → k` finite (the setting of
Artin's Axioms, Section 07WY), and let `x₀` be an object of `𝒳 = Complexes_{X/B}` over
`Spec k`. Then the tangent space `T𝓕_{𝒳,k,x₀}` and the infinitesimal automorphisms
`Inf(𝓕_{𝒳,k,x₀})` (at every `x` and `P`) are finite dimensional over `k`. -/
theorem finiteDimensional_tangentSpaceModuleOfSatisfiesRS_proved
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from D.Y.obj))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    FiniteDimensional k (tangentSpaceModuleOfSatisfiesRS B S hS (complexesFunctor D)
        (complexesFunctor_isFiberedInGroupoids D) (satisfiesRS_complexesFunctor_proved D) iΛ x₀
        hx₀ hfinite hqc) ∧
      ∀ x P, FiniteDimensional k (infinitesimalAutomorphismModuleOfSatisfiesRS B S hS
        (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D)
        (satisfiesRS_complexesFunctor_proved D) iΛ x₀ hx₀ hfinite hqc x P) := by
  have hk : B.Contains (Spec (.of k)) := contains_spec_of_fieldPoint hx₀
  have hT𝒲 : FibreTangentFinite D iΛ x₀ hx₀ :=
    fibreTangentFinite_of_fibreLiftClassPullback_finiteExt D
      (complexesFunctor_isFiberedInGroupoids D) (satisfiesRSStar_complexesFunctor_proved D) iΛ x₀
      hx₀ hfinite hqc hk
      (hDer := fun _ => (HasDerivedCategory.standard _ : HasDerivedCategory.{u + 1} _))
      (fun hK m hKm => fibreLiftClassPullback (hDer := fun _ => HasDerivedCategory.standard _) hK m
        hKm)
  have hInf𝒲 : FibreInfFinite D iΛ x₀ hx₀ :=
    fibreInfFinite_of_fibreTrivialAutNatural_finiteExt D
      (satisfiesRSStar_complexesFunctor_proved D) iΛ x₀ hx₀ hk
      (hDer := fun _ => (HasDerivedCategory.standard _ : HasDerivedCategory.{u + 1} _))
      (fun hK => fibreTrivialAutNatural_of_fibreLiftAutPullback
        (hDer := fun _ => HasDerivedCategory.standard _) (complexesFunctor_isFiberedInGroupoids D)
        hK (fibreLiftAutPullback (hDer := fun _ => HasDerivedCategory.standard _) hK))
  exact finiteDimensional_tangentSpaceModuleOfSatisfiesRS_of_isOpenImmersion D hft
    (complexesFunctor_isFiberedInGroupoids D) (satisfiesRS_complexesFunctor_proved D) iΛ hiΛ x₀
    hx₀ hfinite hqc hT𝒲 hInf𝒲

end TangentSpace

end AlgebraicGeometry.Space.ComplexesSituation

end
