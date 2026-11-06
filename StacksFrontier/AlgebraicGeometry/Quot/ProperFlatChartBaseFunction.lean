module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartBaseMap
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblemSections
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMapGlobalSection

/-!
# Functions of `Spec A'` in the thickened base of the problem at a chart

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart and `D` a
square-zero thickening `Spec A ⊂ Spec A'` of Situation 07YX. A function `a` of `Spec A'` gives a
global section of the thickened base `𝒪'` of `Spec A` over which
`AlgebraicGeometry.Space.ProperFlatLift.problemOnChart x hx D` is posed
(`AlgebraicGeometry.Space.ProperFlatLift.chartThickenedBaseFunction`). For a morphism of
thickenings `h : D₁ ⟶ D₂`, the map of thickened bases
`AlgebraicGeometry.Space.ProperFlatLift.chartBaseExtensionMap` carries the function `a` of
`Spec A'₁` to the function `h(a)` of `Spec A'₂`, and so does its inverse image along
`f : X → Spec A`, on the model.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

attribute [local instance high]
  AlgebraicGeometry.Space.preservesFiniteProducts_smallEtalePostcomp_AlgebraExtensionEtaleRestriction
  AlgebraicGeometry.Space.hasLimitsOfShape_discrete_EtaleRestrictionInverseImageGlobalSection
  AlgebraicGeometry.Space.hasTerminal_topos_EtaleRestrictionInverseImageGlobalSection
  AlgebraicGeometry.Space.hasLimitsOfShape_discreteF_ProperFlatDeformationMapGlobalSection
  AlgebraicGeometry.Space.hasLimitsOfShape_discrete₀_ProperFlatDeformationMapGlobalSection
  AlgebraicGeometry.Space.hasDiscreteLimits_topos_ProperFlatDeformationMapGlobalSection
  AlgebraicGeometry.Space.hasTerminal_topos_ProperFlatDeformationMapGlobalSection

-- Lean v4.35.0: `HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u)` (for `⊤_ Sheaf J (Type u)`)
-- exceeds the default typeclass budget.
set_option synthInstance.maxHeartbeats 400000

/-- File-local shortcut: the inverse image of a morphism of topoi preserves finite products
(instance search through the generic paths times out). -/
local instance (priority := high) preservesFiniteProducts_inverseImage_properFlatChartBaseFunction
    {E : Type*} [Category E] {F : Type*} [Category F] (f : MorphismOfTopoi E F) :
    PreservesFiniteProducts f.inverseImage :=
  haveI := f.preservesFiniteLimits
  inferInstance

/-- File-local shortcut: the inverse image of a morphism of topoi preserves the terminal
object (instance search through the generic paths times out). -/
local instance (priority := high) isIso_terminalComparison_inverseImage_properFlatChartBaseFunction
    {E : Type*} [Category E] {F : Type*} [Category F] [HasTerminal E] [HasTerminal F]
    (f : MorphismOfTopoi E F) : IsIso (terminalComparison f.inverseImage) :=
  haveI := f.preservesFiniteLimits
  inferInstance

universe u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin Deformation.ToposThickening

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')

/-- Postcomposition with the isomorphism `chartRangeIso D` onto the base subspace of `Spec A'` is
continuous for the small étale topologies. -/
local instance chartRangeIso_isContinuous {A' : Type u} [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A') :
    (smallEtalePostcomp B S hS (chartRangeIso D).hom
      (isEtale_hom_of_iso B S hS (chartRangeIso D))).IsContinuous
      (SmallEtale.topology B S hS (schemeSpace (algebraOver A B S hS toS hA)).1)
      (SmallEtale.topology B S hS
        (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
          (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ :
            AlgebraicSpaces B S hS).1) :=
  smallEtalePostcomp_isContinuous B S hS _ _

/-- Postcomposition with the isomorphism `chartRangeIso D` onto the base subspace of `Spec A'` is
cocontinuous for the small étale topologies. -/
local instance chartRangeIso_isCocontinuous {A' : Type u} [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A') :
    (smallEtalePostcomp B S hS (chartRangeIso D).hom
      (isEtale_hom_of_iso B S hS (chartRangeIso D))).IsCocontinuous
      (SmallEtale.topology B S hS (schemeSpace (algebraOver A B S hS toS hA)).1)
      (SmallEtale.topology B S hS
        (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
          (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ :
            AlgebraicSpaces B S hS).1) :=
  smallEtalePostcomp_isCocontinuous B S hS _ _

/-- **The function `a` of `Spec A'`, read in the thickened base `𝒪'` of `Spec A`**: the restriction
along `ρ : Spec A ≅ Z` of the inverse image along `Z ⊂ Spec A'` of the global section `a`, on
underlying sheaves of sets. -/
abbrev chartThickenedBaseFunction (a : baseRing B S hS (Over.mk D.toS')) :
    ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS (schemeSpace (algebraOver A B S hS toS hA)).1)
      (forget CommRingCat.{u})).obj (chartBaseExtension D).extension :=
  (smallEtaleSetRestriction B S hS (chartRangeIso D).hom
    (isEtale_hom_of_iso B S hS (chartRangeIso D))).globalSectionMap
    (Functor.globalSectionMap (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS _
        (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)))).toToposHom.inverseImage
      (ringOneHom (structureRingSheaf B S hS (schemeSpace (Over.mk D.toS'))) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace (Over.mk D.toS')))).map
          (unitModuleMul B S hS (schemeSpace (Over.mk D.toS'))
            (globalFunctionsOfMap (𝟙 (schemeSpace (Over.mk D.toS'))) a))))

/-- `AlgebraicGeometry.Space.ProperFlatLift.chartThickenedBaseFunction` read through
`(ρ ≫ i)⁻¹𝒪_{Spec A'} ≅ (i⁻¹𝒪_{Spec A'})|_{Spec A}`. -/
theorem chartThickenedBaseFunction_eq (a : baseRing B S hS (Over.mk D.toS')) :
    chartThickenedBaseFunction D a =
      Functor.globalSectionMap (smallEtaleRingedToposHom B S hS ((chartRangeIso D).hom ≫
          subspaceInclusion B S hS _
            (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)))).toToposHom.inverseImage
          (ringOneHom (structureRingSheaf B S hS (schemeSpace (Over.mk D.toS'))) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace (Over.mk D.toS')))).map
              (unitModuleMul B S hS (schemeSpace (Over.mk D.toS'))
                (globalFunctionsOfMap (𝟙 (schemeSpace (Over.mk D.toS'))) a)) :
            ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS
              ((schemeSpaceFunctor B S hS).obj (Over.mk D.toS')).1)
              (forget CommRingCat.{u})).obj
                (smallEtaleRingedTopos B S hS
                  ((schemeSpaceFunctor B S hS).obj (Over.mk D.toS'))).O) ≫
        (sheafCompose (SmallEtale.topology B S hS (schemeSpace (algebraOver A B S hS toS hA)).1)
          (forget CommRingCat.{u})).map
          (etaleRestrictionRingComparison B S hS (chartRangeIso D).hom
            (isEtale_hom_of_iso B S hS (chartRangeIso D))
            (subspaceInclusion B S hS _
              (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)))).α.hom :=
  (globalSectionMap_comp_forget_map_etaleRestrictionRingComparison_α_hom B S hS
    (chartRangeIso D).hom (isEtale_hom_of_iso B S hS (chartRangeIso D))
    (subspaceInclusion B S hS _ (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)))
    _).symm

variable {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] {D₁ : SquareZeroThickening A B S hS toS hA A₁}
  {D₂ : SquareZeroThickening A B S hS toS hA A₂} (h : SquareZeroThickening.Hom D₁ D₂)

/-- **The map of thickened bases on functions of `Spec A'`**: `chartBaseExtensionMap h` carries the
function `a` of `Spec A'₁` to the function `h(a)` of `Spec A'₂`, on underlying sheaves of sets. -/
theorem chartThickenedBaseFunction_comp_forget_map_chartBaseExtensionMap
    (a : baseRing B S hS (Over.mk D₁.toS')) :
    chartThickenedBaseFunction D₁ a ≫
        (sheafCompose (SmallEtale.topology B S hS (schemeSpace (algebraOver A B S hS toS hA)).1)
          (forget CommRingCat.{u})).map (chartBaseExtensionMap h) =
      chartThickenedBaseFunction D₂
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h.overMap).op).hom a) := by
  have hI := globalSectionMap_comp_forget_map_etaleRestrictionInverseImageMap B S hS
    (chartRangeIso D₁).hom (isEtale_hom_of_iso B S hS (chartRangeIso D₁))
    (subspaceInclusion B S hS _ (baseSubspace D₁.arrow (isSquareZeroClosedImmersion_arrow D₁)))
    (chartRangeIso D₂).hom (isEtale_hom_of_iso B S hS (chartRangeIso D₂))
    (subspaceInclusion B S hS _ (baseSubspace D₂.arrow (isSquareZeroClosedImmersion_arrow D₂)))
    (schemeSpaceMap h.overMap) (chartRangeIso_comp_overMap h)
    (ringOneHom (structureRingSheaf B S hS (schemeSpace (Over.mk D₁.toS'))) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace (Over.mk D₁.toS')))).map
        (unitModuleMul B S hS (schemeSpace (Over.mk D₁.toS'))
          (globalFunctionsOfMap (𝟙 (schemeSpace (Over.mk D₁.toS'))) a)))
  have hC := globalSectionMap_unitModuleMul_globalFunctionsOfMap_comp_structureSharpInverseImage
    B S hS (schemeSpaceMap h.overMap) (𝟙 (schemeSpace (Over.mk D₁.toS'))) a
  have hF : globalFunctionsOfMap (schemeSpaceMap h.overMap ≫ 𝟙 (schemeSpace (Over.mk D₁.toS'))) a =
      globalFunctionsOfMap (𝟙 (schemeSpace (Over.mk D₂.toS')))
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h.overMap).op).hom a) :=
    (congrArg (fun f : schemeSpace (Over.mk D₂.toS') ⟶ schemeSpace (Over.mk D₁.toS') =>
        globalFunctionsOfMap f a)
      ((Category.comp_id _).trans (Category.id_comp _).symm)).trans
      (globalFunctionsOfMap_comp B S hS _ _ a)
  refine (congrArg (· ≫ (sheafCompose (SmallEtale.topology B S hS
    (schemeSpace (algebraOver A B S hS toS hA)).1) (forget CommRingCat.{u})).map
      (chartBaseExtensionMap h)) (chartThickenedBaseFunction_eq D₁ a)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((sheafCompose (SmallEtale.topology B S hS
    (schemeSpace (algebraOver A B S hS toS hA)).1) (forget CommRingCat.{u})).map_comp
      _ _).symm).trans ?_
  refine hI.trans ?_
  refine Eq.trans ?_ (chartThickenedBaseFunction_eq D₂ _).symm
  refine congrArg (fun t => (smallEtaleRingedToposHom B S hS ((chartRangeIso D₂).hom ≫
      subspaceInclusion B S hS _ (baseSubspace D₂.arrow
        (isSquareZeroClosedImmersion_arrow D₂)))).toToposHom.inverseImage.globalSectionMap t ≫
      (sheafCompose (SmallEtale.topology B S hS (schemeSpace (algebraOver A B S hS toS hA)).1)
        (forget CommRingCat.{u})).map
        (etaleRestrictionRingComparison B S hS (chartRangeIso D₂).hom
          (isEtale_hom_of_iso B S hS (chartRangeIso D₂))
          (subspaceInclusion B S hS _
            (baseSubspace D₂.arrow (isSquareZeroClosedImmersion_arrow D₂)))).α.hom) (hC.trans ?_)
  exact congrArg (fun r => ringOneHom (structureRingSheaf B S hS (schemeSpace (Over.mk D₂.toS'))) ≫
    (moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace (Over.mk D₂.toS')))).map
      (unitModuleMul B S hS (schemeSpace (Over.mk D₂.toS')) r)) hF

/-- The function of `Spec A'₂` given by `h(k)` is `h` applied to the function `k` of `Spec A'₁`. -/
theorem Γ_map_overMap_ΓSpecIso_inv (k : D₁.kernel) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h.overMap).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (show RingHom.ker D₁.q from k).1) =
      (Scheme.ΓSpecIso (CommRingCat.of A₂)).inv.hom
        (show RingHom.ker D₂.q from h.kernelMap.hom k).1 := by
  rw [h.kernelMap_spec]
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom h.ringHom)) _).symm

/-- `AlgebraicGeometry.Space.ProperFlatLift.Γ_map_overMap_ΓSpecIso_inv`, with the functions read
in the ideals of `Spec A ⊂ Spec A'ᵢ`. -/
theorem Γ_map_overMap_thickeningKernelIdealIso (k : D₁.kernel) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h.overMap).op).hom
        ((thickeningKernelIdealIso D₁).hom.hom k).1 =
      ((thickeningKernelIdealIso D₂).hom.hom (h.kernelMap.hom k)).1 :=
  Γ_map_overMap_ΓSpecIso_inv h k

/-- **The inverse image of the map of thickened bases on the generators**: `f⁻¹` of
`chartBaseExtensionMap h` carries the inverse image of the function `k` of `Spec A'₁` to that of
the function `h(k)` of `Spec A'₂`, over every object of the model. -/
theorem inverseImage_chartBaseExtensionMap_chartThickenedBaseFunction (k : D₁.kernel)
    (U : (SmallModel.{u} (SmallEtale B S hS x.obj.obj.left.1))ᵒᵖ)
    (p : (sectionsFunctor (SmallEtale.topology B S hS x.obj.obj.left.1)
      ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.op.obj U)).obj
        (⊤_ Sheaf (SmallEtale.topology B S hS x.obj.obj.left.1) (Type u))) :
    ((inverseImageCommRingFunctor (problemOnChart x hx D₁).f.toToposHom).map
        (chartBaseExtensionMap h)).hom.app U
      (((RingedToposExtensionProblem.siteTransportInverseImageIso
          (smallEtaleModelTopology B S hS x.obj.obj.left.1)
          (smallEtaleModelEquiv B S hS x.obj.obj.left)
          (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom).app
          (chartBaseExtension D₁).extension).inv.hom.app U
        ((sectionsFunctor (SmallEtale.topology B S hS x.obj.obj.left.1)
          ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.op.obj U)).map
          (Functor.globalSectionMap
            (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom.inverseImage
            (chartThickenedBaseFunction D₁ ((thickeningKernelIdealIso D₁).hom.hom k).1)) p)) =
      ((RingedToposExtensionProblem.siteTransportInverseImageIso
          (smallEtaleModelTopology B S hS x.obj.obj.left.1)
          (smallEtaleModelEquiv B S hS x.obj.obj.left)
          (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom).app
          (chartBaseExtension D₂).extension).inv.hom.app U
        ((sectionsFunctor (SmallEtale.topology B S hS x.obj.obj.left.1)
          ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.op.obj U)).map
          (Functor.globalSectionMap
            (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom.inverseImage
            (chartThickenedBaseFunction D₂
              ((thickeningKernelIdealIso D₂).hom.hom (h.kernelMap.hom k)).1)) p) := by
  have hnat := (RingedToposExtensionProblem.siteTransportInverseImageIso
      (smallEtaleModelTopology B S hS x.obj.obj.left.1)
      (smallEtaleModelEquiv B S hS x.obj.obj.left)
      (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom).inv.naturality
        (chartBaseExtensionMap h)
  have hn := ConcreteCategory.congr_hom (congrArg (fun m => m.hom.app U) hnat)
    ((sectionsFunctor (SmallEtale.topology B S hS x.obj.obj.left.1)
          ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.op.obj U)).map
      (Functor.globalSectionMap
        (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom.inverseImage
        (chartThickenedBaseFunction D₁ ((thickeningKernelIdealIso D₁).hom.hom k).1)) p)
  refine hn.symm.trans ?_
  refine congrArg (fun y => ((RingedToposExtensionProblem.siteTransportInverseImageIso
      (smallEtaleModelTopology B S hS x.obj.obj.left.1)
      (smallEtaleModelEquiv B S hS x.obj.obj.left)
      (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom).app
      (chartBaseExtension D₂).extension).inv.hom.app U y) ?_
  have hf := Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor_map_forget
    (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom (chartBaseExtensionMap h)
  have hb := (chartThickenedBaseFunction_comp_forget_map_chartBaseExtensionMap h
    ((thickeningKernelIdealIso D₁).hom.hom k).1).trans
      (congrArg (chartThickenedBaseFunction D₂) (Γ_map_overMap_thickeningKernelIdealIso h k))
  exact (sectionsFunctor_map_congr (congrArg (fun m =>
      Functor.globalSectionMap
        (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom.inverseImage
        (chartThickenedBaseFunction D₁ ((thickeningKernelIdealIso D₁).hom.hom k).1) ≫ m) hf)
      ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.op.obj U) p).trans
    ((sectionsFunctor_map_congr (Functor.globalSectionMap_comp
      (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom.inverseImage _ _)
        ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.op.obj U) p).trans
      (sectionsFunctor_map_congr (congrArg (Functor.globalSectionMap
        (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toToposHom.inverseImage)
          hb) ((smallEtaleModelEquiv B S hS x.obj.obj.left).inverse.op.obj U) p))

end AlgebraicGeometry.Space.ProperFlatLift
