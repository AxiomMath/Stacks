module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Crystalline.SheafGlobalSectionHom

/-!
# The degree-two canonical map of [Stacks, Tag 07J6] on local pure tensors

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `T''` be the second-order
universal thickening of [Stacks, Remark 60.14.5, Tag 07J3] with first projection `q₀ : T'' ⟶ T`,
and let `N` be a sheaf of `𝒪_T`-modules.  Composing the projection-formula morphism
`Crystalline.secondOrderThickeningProjectionFormulaMap` of [Stacks, Tag 0FZE] with `N` tensored
with the inclusion `η ↦ (0, 0, 0, η)` of the top summand of
`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/Y,δ} ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}` gives

`N ⊗_{𝒪_T} Ω²_{T/Y,δ} ⟶ q₀_*(q₀^* N)`,

the sheaf-level counterpart of the degree-two canonical map
`Crystalline.GlobalCrystallineSituation.diffAction₂` of [Stacks, Tag 07J6],
`η ⊗ x ↦ η · q₀^* x`.  This module computes it on local pure tensors, in the same way and for
the same reason as
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealBraidedSections.lean` does in degree
one: after precomposition with the symmetry constraint, which has no description on local
sections at the spelling in play and which naturality of the braiding moves to the front.

## Main definitions

* `Crystalline.secondOrderBraidedProjectionFormula` — the composite
  `Ω²_{T/Y,δ} ⊗ N ⟶ q₀_*(q₀^* N)` in which no symmetry constraint occurs.

## Main results

* `Crystalline.secondOrderBraidedProjectionFormula_tmul` — **it carries the local pure tensor
  `η ⊗ x` to `(0, 0, 0, η) · q₀^* x`.**
* `Crystalline.whiskerLeft_topInrSheaf_comp_secondOrderThickeningProjectionFormulaMap` — **it is
  the degree-two canonical map precomposed with the symmetry constraint.**

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules braidedCategorySchemeModules

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y) (N : T.scheme.Modules)

/-- **The degree-two canonical map with its two factors in the order in which the symmetry
constraint has cancelled**: the inclusion `η ↦ (0, 0, 0, η)` of the top summand of `𝒪_{T''}`
whiskered on the right by `N`, followed by the projection-formula morphism of
[Stacks, Tag 0FZE] at `q₀` and by the direct image of the left unitor. -/
def secondOrderBraidedProjectionFormula :
    dpSecondExteriorPower T Y f ⊗ N ⟶
      (Scheme.Modules.pushforward (secondOrderThickeningQ₀Hom T Y f)).obj
        ((Scheme.Modules.pullback (secondOrderThickeningQ₀Hom T Y f)).obj N) :=
  (secondOrderThickeningTopInrSheaf T Y f ▷ N) ≫
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
        (secondOrderThickeningQ₀Hom T Y f)
        (SheafOfModules.unit (secondOrderThickeningScheme T Y f).ringCatSheaf) N ≫
      (Scheme.Modules.pushforward (secondOrderThickeningQ₀Hom T Y f)).map
        (λ_ ((Scheme.Modules.pullback (secondOrderThickeningQ₀Hom T Y f)).obj N)).hom

/-- **A local two-form, read as a section of `𝒪_{T''}` over the preimage of the open** through
the top summand.  The identity; the ascription is what lets it be used as a scalar on the
sections of `q₀^* N`. -/
def secondOrderIdealScalar (W : (Opens ↑T.scheme)ᵒᵖ)
    (η : (dpSecondExteriorPower T Y f).val.obj W) :
    ↑((Stacks.RingedSpace.structureRingSheaf
        (secondOrderThickeningScheme T Y f).toRingedSpace).obj.obj
      ((RingedSpaceModuleAdjunction.opensMap
        (secondOrderThickeningQ₀Hom T Y f).toLRSHom.toShHom).op.obj W)) :=
  (secondOrderThickeningTopInrSheaf T Y f).val.app W η

/-- **Whiskering the inclusion of the top summand on the right by `N` carries a local pure
tensor to a local pure tensor**, the first factor read in `q₀_* 𝒪_{T''}` through the top summand.
This is `Stacks.RingedSpace.tensorSheaf_map_unit_tmul` at the pair
`(η ↦ (0, 0, 0, η), 𝟙 N)`; it is a separate declaration because writing the whiskered morphism
applied to a local pure tensor is an expensive elaboration at this spelling, and the integrability
computation needs it three times. -/
theorem secondOrderTopInrSheaf_whiskerRight_tmul (W : (Opens ↑T.scheme)ᵒᵖ)
    (η : (dpSecondExteriorPower T Y f).val.obj W) (x : N.val.obj W) :
    (secondOrderThickeningTopInrSheaf T Y f ▷ N).val.app W
        (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
          (dpSecondExteriorPower T Y f) N W η x) =
      Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
        (secondOrderThickeningUnitRestriction T Y f) N W
        ((secondOrderThickeningTopInrSheaf T Y f).val.app W η) x := by
  have hmap := Stacks.RingedSpace.tensorSheaf_map_unit_tmul T.scheme.toRingedSpace
    (secondOrderThickeningTopInrSheaf T Y f) (𝟙 N) W η x
  exact Eq.trans (PresheafOfModules.hom_congr_apply
    (congrArg (fun k => SheafOfModules.Hom.val k)
      ((Stacks.SheafOfModules.Tensor.sheafTensor_map_app T.scheme.toRingedSpace.sheaf
          (secondOrderThickeningTopInrSheaf T Y f) N).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map T.scheme.toRingedSpace.sheaf
          (secondOrderThickeningTopInrSheaf T Y f) (𝟙 N)).symm)) W _) hmap

/-- **The projection-formula morphism at `q₀` carries the local pure tensor whose first factor is
a section of `q₀_* 𝒪_{T''}` to the corresponding pure tensor upstairs**, by
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul` at the unit module of
`T''`; the first factor is `Crystalline.secondOrderIdealScalar`. -/
theorem projectionFormulaMap_secondOrderTopInr_tmul (W : (Opens ↑T.scheme)ᵒᵖ)
    (η : (dpSecondExteriorPower T Y f).val.obj W) (x : N.val.obj W) :
    (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
          (secondOrderThickeningQ₀Hom T Y f)
          (SheafOfModules.unit (secondOrderThickeningScheme T Y f).ringCatSheaf) N).val.app W
        (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
          (secondOrderThickeningUnitRestriction T Y f) N W
          ((secondOrderThickeningTopInrSheaf T Y f).val.app W η) x) =
      Stacks.PullbackTensorCoherence.tmul (secondOrderThickeningScheme T Y f).toRingedSpace
        (schemeUnitModule (secondOrderThickeningScheme T Y f))
        ((Scheme.Modules.pullback (secondOrderThickeningQ₀Hom T Y f)).obj N)
        ((RingedSpaceModuleAdjunction.opensMap
          (secondOrderThickeningQ₀Hom T Y f).toLRSHom.toShHom).op.obj W)
        (secondOrderIdealScalar T Y f W η)
        (Stacks.RingedSpace.pullbackUnit
          (secondOrderThickeningQ₀Hom T Y f).toLRSHom.toShHom N W x) :=
  Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul
    (secondOrderThickeningQ₀Hom T Y f)
    (SheafOfModules.unit (secondOrderThickeningScheme T Y f).ringCatSheaf) N W
    ((secondOrderThickeningTopInrSheaf T Y f).val.app W η) x

/-- **The degree-two canonical map carries the local pure tensor `η ⊗ x` to
`(0, 0, 0, η) · q₀^* x`.** -/
theorem secondOrderBraidedProjectionFormula_tmul (W : (Opens ↑T.scheme)ᵒᵖ)
    (η : (dpSecondExteriorPower T Y f).val.obj W) (x : N.val.obj W) :
    (secondOrderBraidedProjectionFormula T Y f N).val.app W
        (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
          (dpSecondExteriorPower T Y f) N W η x) =
      secondOrderIdealScalar T Y f W η •
        Stacks.RingedSpace.pullbackUnit
          (secondOrderThickeningQ₀Hom T Y f).toLRSHom.toShHom N W x := by
  have a3 := leftUnitor_val_app (secondOrderThickeningScheme T Y f)
    ((Scheme.Modules.pullback (secondOrderThickeningQ₀Hom T Y f)).obj N)
    ((RingedSpaceModuleAdjunction.opensMap
      (secondOrderThickeningQ₀Hom T Y f).toLRSHom.toShHom).op.obj W)
    (secondOrderIdealScalar T Y f W η)
    (Stacks.RingedSpace.pullbackUnit
      (secondOrderThickeningQ₀Hom T Y f).toLRSHom.toShHom N W x)
  refine Eq.trans (Stacks.SheafOfModules.comp_val_app_apply _ _ W _) ?_
  refine Eq.trans (Stacks.SheafOfModules.comp_val_app_apply _ _ W _) ?_
  exact Eq.trans (congrArg _ (Eq.trans
    (congrArg _ (secondOrderTopInrSheaf_whiskerRight_tmul T Y f N W η x))
    (projectionFormulaMap_secondOrderTopInr_tmul T Y f N W η x))) a3

/-- **The degree-two canonical map of [Stacks, Tag 07J6] is the symmetry constraint followed by
the braiding-free composite.** -/
theorem whiskerLeft_topInrSheaf_comp_secondOrderThickeningProjectionFormulaMap :
    (N ◁ secondOrderThickeningTopInrSheaf T Y f) ≫
        secondOrderThickeningProjectionFormulaMap T Y f N =
      (β_ N (dpSecondExteriorPower T Y f)).hom ≫
        secondOrderBraidedProjectionFormula T Y f N := by
  have h1 : (N ◁ secondOrderThickeningTopInrSheaf T Y f) ≫
        (β_ N (secondOrderThickeningUnitRestriction T Y f)).hom =
      (β_ N (dpSecondExteriorPower T Y f)).hom ≫
        (secondOrderThickeningTopInrSheaf T Y f ▷ N) :=
    BraidedCategory.braiding_naturality_right N (secondOrderThickeningTopInrSheaf T Y f)
  show (N ◁ secondOrderThickeningTopInrSheaf T Y f) ≫
      (β_ N (secondOrderThickeningUnitRestriction T Y f)).hom ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
            (secondOrderThickeningQ₀Hom T Y f)
            (SheafOfModules.unit (secondOrderThickeningScheme T Y f).ringCatSheaf) N ≫
          (Scheme.Modules.pushforward (secondOrderThickeningQ₀Hom T Y f)).map
            (λ_ ((Scheme.Modules.pullback (secondOrderThickeningQ₀Hom T Y f)).obj N)).hom = _
  rw [← Category.assoc, h1, Category.assoc]
  rfl

end Crystalline

end

end
