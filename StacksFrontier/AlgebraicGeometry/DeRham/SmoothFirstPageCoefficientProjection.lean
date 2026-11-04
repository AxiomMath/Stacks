module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageCoefficientFunctors

/-!
# The projection-formula morphism of the first page, natural in the coefficient module

Conclusion (4) of [Stacks, Tag 0FML] at the relative de Rham complex,
`Stacks.DeRhamDirectImage.deRhamOrdinaryProjectionFormulaIso`, is an isomorphism for a
quasi-coherent module `G`. This file records that it is the value of a morphism defined for every
`𝒪_Y`-module `G` and natural in `G`.

## Main definitions

* `Stacks.DeRhamSmooth.coefficientProjectionFormulaMap`: the morphism
  `Rf_*Ω^•_{X/Y} ⊗^𝐋 G ⟶ Rf_*(Ω^•_{X/Y} ⊗ f^{-1}G)` for an arbitrary `G`.

## Main results

* `Stacks.DeRhamSmooth.deRhamOrdinaryProjectionFormulaIso_hom_eq`: for quasi-coherent `G` it is the
  isomorphism of conclusion (4) of Tag 0FML.
* `Stacks.DeRhamSmooth.coefficientProjectionFormulaMap_naturality`: it is natural in `G`.

## References

* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.FilteredComplex (higherDirectImage)

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf


namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

section ProjectionFormula

open Stacks.DerivedTensor.RingedSite Stacks.Cohomology.DerivedProjectionFormula

variable [QuasiCompact f] [QuasiSeparated f] [Smooth f]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The relative de Rham complex of a smooth morphism is K-flat over `f^{-1}𝒪_Y`. -/
theorem kFlat_deRhamCochainComplex :
    Stacks.SheafOfModules.KFlat.KFlat (inverseImageBase f).sheaf (deRhamCochainComplex f) :=
  Stacks.Cohomology.LocallyBoundedKFlat.kFlat_of_isLocallyBounded_of_flat
    (inverseImageBase f) (deRhamCochainComplex f) (isLocallyBounded_deRhamCochainComplex f)
    (isFlat_deRhamCochainComplex_X f)

/-- **The morphism of conclusion (4) of [Stacks, Tag 0FML] at the relative de Rham complex, for
an arbitrary `𝒪_Y`-module `G`**:
`Rf_*Ω^•_{X/Y} ⊗^𝐋_{𝒪_Y} G ⟶ Rf_*(Ω^•_{X/Y} ⊗_{f^{-1}𝒪_Y} f^{-1}G)`, the projection-formula
morphism of [Stacks, Tag 0B53] followed by the identification of its target with the ordinary
tensor complex. For quasi-coherent `G` it is the isomorphism
`Stacks.DeRhamDirectImage.deRhamOrdinaryProjectionFormulaIso`
(`deRhamOrdinaryProjectionFormulaIso_hom_eq`); in general it is a morphism, natural in `G`. -/
def coefficientProjectionFormulaMap (G : Modules Y.toRingedSpace) :
    ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj (deRhamCochainComplex f)))).obj
      ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).obj G) ⟶
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj
              (deRhamCochainComplex f)).obj
            ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)))) :=
  haveI : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_inverseImageModulePullback
      Y.toRingedSpace f.base
  projectionFormulaMap (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj (deRhamCochainComplex f))
      ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).obj G) ≫
    (derivedPushforward (inverseImageBaseProjection f)).map
      (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj (deRhamCochainComplex f))).map
          ((Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
              (inverseImageBaseProjection f) G).hom ≫
            ((DerivedCategory.singleFunctorIsoCompQ (Modules (inverseImageBase f)) 0).app
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)).hom) ≫
        ((canonicalDerivedTensorProduct (inverseImageBase f).sheaf).comparisonLeft
          (deRhamCochainComplex f)
          ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
            ((RingedSpaceModuleAdjunction.modulePullback
              (inverseImageBaseProjection f)).obj G)) (kFlat_deRhamCochainComplex f)).hom)

/-- For quasi-coherent `G`, `coefficientProjectionFormulaMap` is the isomorphism of conclusion
(4) of [Stacks, Tag 0FML] at the relative de Rham complex. -/
theorem deRhamOrdinaryProjectionFormulaIso_hom_eq (G : Modules Y.toRingedSpace)
    (hG : G.IsQuasicoherent) :
    (deRhamOrdinaryProjectionFormulaIso f G hG).hom = coefficientProjectionFormulaMap f G :=
  rfl

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **`coefficientProjectionFormulaMap` is natural in the module.** -/
theorem coefficientProjectionFormulaMap_naturality {G G' : Modules Y.toRingedSpace} (φ : G ⟶ G') :
    ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj (deRhamCochainComplex f)))).map
        ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).map φ) ≫
        coefficientProjectionFormulaMap f G' =
      coefficientProjectionFormulaMap f G ≫
        (derivedPushforward (inverseImageBaseProjection f)).map (DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj
              (deRhamCochainComplex f)).map
            ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).map
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).map φ)))) := by
  have : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_inverseImageModulePullback
      Y.toRingedSpace f.base
  have h₁ := projectionFormulaMap_natural_right (inverseImageBaseProjection f)
    (DerivedCategory.Q.obj (deRhamCochainComplex f))
    ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).map φ)
  have h₂ := Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat_hom_naturality
    (inverseImageBaseProjection f) φ
  have h₃ := (DerivedCategory.singleFunctorIsoCompQ (Modules (inverseImageBase f)) 0).hom.naturality
    ((RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)).map φ)
  have h₄ := (canonicalDerivedTensorProduct (inverseImageBase f).sheaf).comparisonLeft_naturality
    (𝟙 (deRhamCochainComplex f))
    ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).map
      ((RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)).map φ))
    (kFlat_deRhamCochainComplex f) (kFlat_deRhamCochainComplex f)
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h₄
  dsimp only [Functor.comp_map] at h₃
  have inner : ((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
        (DerivedCategory.Q.obj (deRhamCochainComplex f))).map
        ((derivedPullback (inverseImageBaseProjection f)).map
          ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).map φ)) ≫
        ((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj (deRhamCochainComplex f))).map
          ((Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
              (inverseImageBaseProjection f) G').hom ≫
            ((DerivedCategory.singleFunctorIsoCompQ (Modules (inverseImageBase f)) 0).app
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G')).hom) ≫
        ((canonicalDerivedTensorProduct (inverseImageBase f).sheaf).comparisonLeft
          (deRhamCochainComplex f)
          ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
            ((RingedSpaceModuleAdjunction.modulePullback
              (inverseImageBaseProjection f)).obj G')) (kFlat_deRhamCochainComplex f)).hom =
      (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj (deRhamCochainComplex f))).map
          ((Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
              (inverseImageBaseProjection f) G).hom ≫
            ((DerivedCategory.singleFunctorIsoCompQ (Modules (inverseImageBase f)) 0).app
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)).hom) ≫
        ((canonicalDerivedTensorProduct (inverseImageBase f).sheaf).comparisonLeft
          (deRhamCochainComplex f)
          ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
            ((RingedSpaceModuleAdjunction.modulePullback
              (inverseImageBaseProjection f)).obj G)) (kFlat_deRhamCochainComplex f)).hom) ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj
              (deRhamCochainComplex f)).map
            ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).map
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).map φ))) := by
    have key : (derivedPullback (inverseImageBaseProjection f)).map
          ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).map φ) ≫
          (Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
            (inverseImageBaseProjection f) G').hom ≫
          ((DerivedCategory.singleFunctorIsoCompQ (Modules (inverseImageBase f)) 0).app
            ((RingedSpaceModuleAdjunction.modulePullback
              (inverseImageBaseProjection f)).obj G')).hom =
        ((Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
            (inverseImageBaseProjection f) G).hom ≫
          ((DerivedCategory.singleFunctorIsoCompQ (Modules (inverseImageBase f)) 0).app
            ((RingedSpaceModuleAdjunction.modulePullback
              (inverseImageBaseProjection f)).obj G)).hom) ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).map
            ((RingedSpaceModuleAdjunction.modulePullback
              (inverseImageBaseProjection f)).map φ)) := by
      have h₂' : (derivedPullback (inverseImageBaseProjection f)).map
            ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).map φ) ≫
            (Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
              (inverseImageBaseProjection f) G').hom =
          (Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
              (inverseImageBaseProjection f) G).hom ≫
            (DerivedCategory.singleFunctor (Modules (inverseImageBase f)) 0).map
              ((RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)).map φ) :=
        h₂
      simp only [reassoc_of% h₂', Iso.app_hom, h₃, Category.assoc]
    have key' := congrArg ((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
      (DerivedCategory.Q.obj (deRhamCochainComplex f))).map key
    simp only [Functor.map_comp, Category.assoc] at key'
    simp only [Functor.map_comp, Category.assoc, reassoc_of% key']
    exact congrArg _ (congrArg _ h₄)
  have inner' := congrArg (derivedPushforward (inverseImageBaseProjection f)).map inner
  simp only [Functor.map_comp, Category.assoc] at inner'
  simp only [coefficientProjectionFormulaMap, Category.assoc, Functor.map_comp]
  simp only [reassoc_of% h₁, inner']

end ProjectionFormula

end Stacks.DeRhamSmooth

end
