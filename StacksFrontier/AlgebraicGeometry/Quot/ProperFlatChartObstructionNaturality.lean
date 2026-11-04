module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartBaseMap
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionBaseNaturality

/-!
# Naturality of the obstruction class at a chart

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart. For a
square-zero thickening `D` of Situation 07YX the obstruction class
`o(D) ∈ T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` is the class of [Stacks, Tag 08V5] of the
extension problem `AlgebraicGeometry.Space.ProperFlatLift.problemOnChart x hx D`, posed over
`Spec A`. For a morphism `h : D₁ ⟶ D₂` of thickenings, the two problems share the morphism
`X → Spec A` and the middle ring `f⁻¹𝒪_{Spec A}`. The map of thickened bases
(`AlgebraicGeometry.Space.ProperFlatLift.chartBaseExtensionMap`), the map of ideals
(`AlgebraicGeometry.Space.ProperFlatLift.problemOnChartIdealMap`) and the compatibility of the
prescribed maps with `𝒪_X ⊗ h.kernelMap` make `h` a morphism of extension problems.
This file shows that then `T²(h.kernelMap)` carries `o(D₁)` to `o(D₂)`: the naturality of
obstruction elements in condition (ii) of [Stacks, Tag 07YX], in the form
`Deformation.Artin.FunctorDeformationTheory.obstructionNatural` asks for.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.cotangentExtTwo_map_chartObstruction`:
  `T²(h.kernelMap)(o(D₁)) = o(D₂)`.

## References

* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

/-- The map of ideals `problemOnChartIdealMap h x hx` of the problems at a chart, as a function
on the sections over `U`. -/
def problemOnChartIdealMapFun {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    {D₁ : SquareZeroThickening A B S hS toS hA A₁} {D₂ : SquareZeroThickening A B S hS toS hA A₂}
    (h : SquareZeroThickening.Hom D₁ D₂) (U : (modelTopos x.obj.obj.left).Cᵒᵖ) :
    (problemOnChart x hx D₁).I.val.obj U → (problemOnChart x hx D₂).I.val.obj U :=
  fun a => (problemOnChartIdealMap h x hx).val.app U a

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The obstruction class at a chart is natural in the thickening.** Let `h : D₁ ⟶ D₂` be a
morphism of square-zero thickenings of Situation 07YX. It gives a morphism of the extension
problems `problemOnChart x hx D₁ ⟶ problemOnChart x hx D₂`: the map of thickened bases
`chartBaseExtensionMap h`, the induced map of ideals `problemOnChartIdealMap h x hx` (on sections,
`problemOnChartIdealMapFun`), and, given as `hk`, the compatibility
`c₂ ∘ ι = (𝒪_X ⊗ h.kernelMap) ∘ c₁` of the prescribed maps.
Then `T²(h.kernelMap)` carries `o(D₁)` to `o(D₂)`. -/
theorem cotangentExtTwo_map_chartObstruction {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    {D₁ : SquareZeroThickening A B S hS toS hA A₁} {D₂ : SquareZeroThickening A B S hS toS hA A₂}
    (h : SquareZeroThickening.Hom D₁ D₂)
    (hk : ∀ (U : (modelTopos x.obj.obj.left).Cᵒᵖ) (a : (problemOnChart x hx D₁).I.val.obj U),
      (show (problemOnChart x hx D₂).G.val.obj U from
          (problemOnChart x hx D₂).c.val.app U (problemOnChartIdealMapFun x hx h U a)) =
        ((modelTensorFunctor (chartBaseRingHom x hx)).map h.kernelMap).val.app U
          (show (problemOnChart x hx D₁).G.val.obj U from
            (problemOnChart x hx D₁).c.val.app U a)) :
    (cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)).map h.kernelMap
        (chartObstruction x hx D₁) = chartObstruction x hx D₂ := by
  apply (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 2
    D₂.kernel).injective
  have hn :=
    Deformation.ToposThickening.RingedToposExtensionProblem.canonicalObstructionClass_comp_map
      (S := problemOnChart x hx D₁) (T := problemOnChart x hx D₂) (problemOnChart_f x hx D₁)
      (problemOnChart_f x hx D₂)
      (chartBaseExtensionMap h) (chartBaseExtensionMap_comp_reduction h)
      ((modelTensorFunctor (chartBaseRingHom x hx)).map h.kernelMap)
      (problemOnChartIdealMapFun x hx h)
      (problemOnChartIdealMap_spec h x hx) hk
  exact (cotangentExtFunctorObjEquiv_map _ _ 2 h.kernelMap _).trans
    ((congrArg (· ≫ _) (cotangentExtFunctorObjEquiv_chartObstruction x hx D₁)).trans
      (((Category.id_comp _).symm.trans (hn.trans (Category.id_comp _))).trans
        (cotangentExtFunctorObjEquiv_chartObstruction x hx D₂).symm))

end AlgebraicGeometry.Space.ProperFlatLift

end
