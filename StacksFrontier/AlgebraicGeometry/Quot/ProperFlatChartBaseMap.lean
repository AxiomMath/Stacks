module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblem
public import StacksFrontier.Deformation.ToposThickening.BaseRowAlgebraExtension

/-!
# The map of thickened bases of `problemOnChart` along a morphism of thickenings

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart, and let
`h : D₁ ⟶ D₂` be a morphism of square-zero thickenings of Situation 07YX: a ring map
`A'₁ → A'₂` over `A` and over the base, so that `Spec A'₂ → Spec A'₁` is a morphism under
`Spec A`. The extension problem `problemOnChart x hx D` of a lift of `x` along `D`, posed over
`Spec A`, has thickened base `𝒪'_D = (j_D⁻¹𝒪_{Spec A'})|_{Spec A}`, `j_D : Spec A ⊂ Spec A'`.

This file constructs the map `𝒪'_{D₁} ⟶ 𝒪'_{D₂}` of thickened bases over `𝒪_{Spec A}`
induced by `Spec A'₂ → Spec A'₁` (`AlgebraicGeometry.Space.ProperFlatLift.chartBaseExtensionMap`),
and the map of ideals `ι : f⁻¹𝒥_{D₁} ⟶ f⁻¹𝒥_{D₂}` it induces on the model of the small étale site
of `X` (`AlgebraicGeometry.Space.ProperFlatLift.problemOnChartIdealMap`). These are the data
`φ`, `ι` along which a solution of `problemOnChart x hx D₂` is read over the thickened base of
`problemOnChart x hx D₁`
(`RingedToposExtensionProblem.CompatibleFirstOrderThickening.restrictBase`).

## Main definitions

* `Deformation.Artin.SquareZeroThickening.Hom.overMap`: `Spec A'₂ ⟶ Spec A'₁` over `S`.
* `AlgebraicGeometry.Space.ProperFlatLift.chartBaseExtensionMap`
* `AlgebraicGeometry.Space.ProperFlatLift.problemOnChartIdealMap`

## References

* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Tag 08V3](https://stacks.math.columbia.edu/tag/08V3)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe u

namespace Deformation.Artin

open AlgebraicGeometry

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))} {A₁ A₂ : Type u} [CommRing A₁]
  [CommRing A₂] {D₁ : SquareZeroThickening A B S hS toS hA A₁}
  {D₂ : SquareZeroThickening A B S hS toS hA A₂}

/-- **The morphism `Spec A'₂ ⟶ Spec A'₁` over `S`** of a morphism of square-zero thickenings
`A'₁ → A'₂`. -/
def SquareZeroThickening.Hom.overMap (h : SquareZeroThickening.Hom D₁ D₂) :
    (Over.mk D₂.toS' : AlgebraicGeometry.BigFppfOver B S hS) ⟶ Over.mk D₁.toS' :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom h.ringHom)) :
    B.obj D₂.hA' ⟶ B.obj D₁.hA') (ObjectProperty.hom_ext _ h.overS)

/-- **`Spec A ⊂ Spec A'₂ → Spec A'₁` is `Spec A ⊂ Spec A'₁`**: the ring map lies over `A`. -/
theorem SquareZeroThickening.Hom.arrow_comp_overMap (h : SquareZeroThickening.Hom D₁ D₂) :
    D₂.arrow ≫ h.overMap = D₁.arrow := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show B.inclusion.map D₂.arrow.left ≫ Spec.map (CommRingCat.ofHom h.ringHom) =
    B.inclusion.map D₁.arrow.left
  rw [D₂.arrow_spec, D₁.arrow_spec]
  exact (Spec.map_comp _ _).symm.trans
    (congrArg (fun φ : A₁ →+* A => Spec.map (CommRingCat.ofHom φ)) h.overBase)

end Deformation.Artin

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin Deformation.ToposThickening

attribute [local instance] restrictedFirstOrderExtension_isContinuous

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] {D₁ : SquareZeroThickening A B S hS toS hA A₁}
  {D₂ : SquareZeroThickening A B S hS toS hA A₂} (h : SquareZeroThickening.Hom D₁ D₂)

/-- `Spec A ≅ Z₂ ⊂ Spec A'₂ → Spec A'₁` is `Spec A ≅ Z₁ ⊂ Spec A'₁`. -/
theorem chartRangeIso_comp_overMap :
    ((chartRangeIso D₂).hom ≫ subspaceInclusion B S hS _
        (baseSubspace D₂.arrow (isSquareZeroClosedImmersion_arrow D₂))) ≫
        schemeSpaceMap h.overMap =
      (chartRangeIso D₁).hom ≫ subspaceInclusion B S hS _
        (baseSubspace D₁.arrow (isSquareZeroClosedImmersion_arrow D₁)) := by
  refine ((congrArg (· ≫ schemeSpaceMap h.overMap)
    (rangeSpaceIso_hom_comp_subspaceInclusion B S hS D₂.arrow
      (isSquareZeroClosedImmersion_arrow D₂).1)).trans ?_).trans
    (rangeSpaceIso_hom_comp_subspaceInclusion B S hS D₁.arrow
      (isSquareZeroClosedImmersion_arrow D₁).1).symm
  exact ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
    (congrArg yoneda.map h.arrow_comp_overMap))

/-- **The map of thickened bases of `problemOnChart` along `h`**: the map
`(j₁⁻¹𝒪_{Spec A'₁})|_{Spec A} ⟶ (j₂⁻¹𝒪_{Spec A'₂})|_{Spec A}` of restricted inverse images given
by `Spec A'₂ → Spec A'₁` (`AlgebraicGeometry.Space.etaleRestrictionInverseImageMap`). -/
def chartBaseExtensionMap :
    (chartBaseExtension D₁).extension ⟶ (chartBaseExtension D₂).extension :=
  etaleRestrictionInverseImageMap B S hS (chartRangeIso D₁).hom
    (isEtale_hom_of_iso B S hS (chartRangeIso D₁))
    (subspaceInclusion B S hS _ (baseSubspace D₁.arrow (isSquareZeroClosedImmersion_arrow D₁)))
    (chartRangeIso D₂).hom (isEtale_hom_of_iso B S hS (chartRangeIso D₂))
    (subspaceInclusion B S hS _ (baseSubspace D₂.arrow (isSquareZeroClosedImmersion_arrow D₂)))
    (schemeSpaceMap h.overMap) (chartRangeIso_comp_overMap h)

/-- The map of thickened bases lies over `𝒪_{Spec A}`. -/
theorem chartBaseExtensionMap_comp_reduction :
    chartBaseExtensionMap h ≫ (chartBaseExtension D₂).reduction =
      (chartBaseExtension D₁).reduction := by
  rw [restrictedFirstOrderExtension_reduction, restrictedFirstOrderExtension_reduction]
  exact etaleRestrictionInverseImageMap_comp_reduction B S hS _ _ _ _ _ _ _ _

variable (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

/-- The inverse image of the map of thickened bases lies over `f⁻¹𝒪_{Spec A}`, read on the lower
rows of `problemOnChart`. -/
theorem inverseImage_chartBaseExtensionMap_comp_reduction :
    (inverseImageCommRingFunctor (problemOnChart x hx D₁).f.toToposHom).map
        (chartBaseExtensionMap h) ≫ (problemOnChart x hx D₂).baseRowExtension.reduction =
      (problemOnChart x hx D₁).baseRowExtension.reduction :=
  ((inverseImageCommRingFunctor (problemOnChart x hx D₁).f.toToposHom).map_comp _ _).symm.trans
    (congrArg (inverseImageCommRingFunctor (problemOnChart x hx D₁).f.toToposHom).map
      (chartBaseExtensionMap_comp_reduction h))

/-- **The map of ideals of `problemOnChart` along `h`**: the map `f⁻¹𝒥_{D₁} ⟶ f⁻¹𝒥_{D₂}` induced
on the kernels of the lower rows by `f⁻¹` of the map of thickened bases. -/
def problemOnChartIdealMap : (problemOnChart x hx D₁).I ⟶ (problemOnChart x hx D₂).I :=
  Deformation.AlgebraExtension.inducedKernelMap (J := (modelTopos x.obj.obj.left).J)
    (problemOnChart x hx D₁).baseRowExtension
    (problemOnChart x hx D₂).baseRowExtension
    ((inverseImageCommRingFunctor (problemOnChart x hx D₁).f.toToposHom).map
      (chartBaseExtensionMap h))
    (inverseImage_chartBaseExtensionMap_comp_reduction h x hx)

/-- **The map of ideals is compatible with the map of thickened bases**, in the form taken by
`RingedToposExtensionProblem.CompatibleFirstOrderThickening.restrictBase`. -/
theorem problemOnChartIdealMap_spec (U : (modelTopos x.obj.obj.left).Cᵒᵖ)
    (a : (problemOnChart x hx D₁).I.val.obj U) :
    ((inverseImageCommRingFunctor (problemOnChart x hx D₁).f.toToposHom).map
        (chartBaseExtensionMap h)).hom.app U
        (show ((inverseImageCommRingFunctor (problemOnChart x hx D₁).f.toToposHom).obj
          (problemOnChart x hx D₁).baseExtension).obj.obj U from
          (problemOnChart x hx D₁).idealInclusion.val.app U a) =
      (show ((inverseImageCommRingFunctor (problemOnChart x hx D₂).f.toToposHom).obj
          (problemOnChart x hx D₂).baseExtension).obj.obj U from
        (problemOnChart x hx D₂).idealInclusion.val.app U
          ((problemOnChartIdealMap h x hx).val.app U a)) :=
  Deformation.AlgebraExtension.hom_incl (problemOnChart x hx D₁).baseRowExtension
    (problemOnChart x hx D₂).baseRowExtension _
    (inverseImage_chartBaseExtensionMap_comp_reduction h x hx) a

end AlgebraicGeometry.Space.ProperFlatLift

end
