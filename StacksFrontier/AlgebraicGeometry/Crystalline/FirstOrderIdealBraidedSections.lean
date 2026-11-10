module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderProjectionFormulaUnitSection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SheafGlobalSectionHom

/-!
# The degree-one canonical map of [Stacks, Tag 07J6] on local pure tensors

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `T'` be the first-order
universal thickening of [Stacks, Tag 07J2] with projection `p₀ : T' ⟶ T`, and let `N` be a sheaf
of `𝒪_T`-modules.  `Crystalline.firstOrderThickeningProjectionFormulaMap` is the comparison
morphism `N ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_*(p₀^* N)` of [Stacks, Tag 0FZE].  Composing it with `N`
tensored with the inclusion `ω ↦ (0, ω)` of the ideal of the diagonal gives the morphism

`N ⊗_{𝒪_T} Ω_{T/Y,δ} ⟶ p₀_*(p₀^* N)`

which is the sheaf-level counterpart of the canonical map
`Crystalline.GlobalCrystallineSituation.diffAction` of [Stacks, Tag 07J6],
`ω ⊗ x ↦ ω · p₀^* x`.  This module computes it on local pure tensors.

## The symmetry constraint, and why the computation is done in the other order

`Crystalline.firstOrderThickeningProjectionFormulaMap` begins with the symmetry constraint of
the monoidal structure on `Mod(𝒪_T)`, and that constraint has **no description on local
sections** at the spelling in play: `Crystalline.monoidalCategorySchemeModules` is a *re-seating*
of the localized monoidal structure, so its braiding is the braiding of the localized structure
conjugated by the re-seating isomorphism, and only the two unitors of the re-seated structure
have been identified with the unitors of the tensor product sheaf
(`Stacks.RingedSpace.leftUnitor_sheafTensor_eq` and its sibling).

So the computation is carried out **after precomposing with the symmetry constraint**, where it
cancels: by naturality of the braiding and its own symmetry,

`(β_ Ω N) ≫ (N ◁ inr) ≫ (β_ N G) = (inr ▷ N)`,

and `Crystalline.firstOrderBraidedProjectionFormula` is the resulting braiding-free composite.
Since the symmetry constraint is an isomorphism, every identity about the map with its two
factors in the original order follows from the corresponding identity about this one.

## Main definitions

* `Crystalline.firstOrderBraidedProjectionFormula` — the composite
  `Ω_{T/Y,δ} ⊗ N ⟶ p₀_*(p₀^* N)`: the inclusion of the ideal of the diagonal whiskered on the
  right by `N`, followed by the projection-formula morphism of [Stacks, Tag 0FZE] and by the
  direct image of the left unitor.  No symmetry constraint occurs in it.

## Main results

* `Crystalline.firstOrderBraidedProjectionFormula_tmul` — **it carries the local pure tensor
  `ω ⊗ x` to `(0, ω) · p₀^* x`**, the section of `𝒪_{T'}` cut out by `ω` acting on the pullback
  of `x`.
* `Crystalline.braiding_comp_whiskerLeft_inrSheaf_comp_projectionFormulaMap` — **it is the
  canonical map of [Stacks, Tag 07J6] precomposed with the symmetry constraint.**

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
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

/-- **The degree-one canonical map with its two factors in the order in which the symmetry
constraint has cancelled**: the inclusion `ω ↦ (0, ω)` of the ideal of the diagonal whiskered on
the right by `N`, followed by the projection-formula morphism of [Stacks, Tag 0FZE] at `p₀` and
by the direct image of the left unitor. -/
def firstOrderBraidedProjectionFormula :
    dpDifferentialsSheaf T Y f ⊗ N ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).obj
        ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N) :=
  (firstOrderThickeningInrSheaf T Y f ▷ N) ≫
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
        (firstOrderThickeningProjHom T Y f)
        (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N ≫
      (Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).map
        (λ_ ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)).hom

/-- **A local section of the ideal of the diagonal, read as a section of `𝒪_{T'}` over the
preimage of the open.**  The identity; the two types are definitionally equal, and the
ascription is what lets the section be used as a scalar on the sections of `p₀^* N`. -/
def firstOrderIdealScalar (W : (Opens ↑T.scheme)ᵒᵖ)
    (ω : (dpDifferentialsSheaf T Y f).val.obj W) :
    ↑((Stacks.RingedSpace.structureRingSheaf
        (firstOrderThickeningScheme T Y f).toRingedSpace).obj.obj
      ((RingedSpaceModuleAdjunction.opensMap
        (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)) :=
  (firstOrderThickeningInrSheaf T Y f).val.app W ω

/-- **The degree-one canonical map carries the local pure tensor `ω ⊗ x` to
`(0, ω) · p₀^* x`.** -/
theorem firstOrderBraidedProjectionFormula_tmul (W : (Opens ↑T.scheme)ᵒᵖ)
    (ω : (dpDifferentialsSheaf T Y f).val.obj W) (x : N.val.obj W) :
    (firstOrderBraidedProjectionFormula T Y f N).val.app W
        (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
          (dpDifferentialsSheaf T Y f) N W ω x) =
      firstOrderIdealScalar T Y f W ω •
        Stacks.RingedSpace.pullbackUnit
          (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W x := by
  have a2 := Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul
    (firstOrderThickeningProjHom T Y f)
    (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N W
    ((firstOrderThickeningInrSheaf T Y f).val.app W ω) x
  have a3 := leftUnitor_val_app (firstOrderThickeningScheme T Y f)
    ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)
    ((RingedSpaceModuleAdjunction.opensMap
      (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)
    (firstOrderIdealScalar T Y f W ω)
    (Stacks.RingedSpace.pullbackUnit
      (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W x)
  have b1 : (firstOrderThickeningInrSheaf T Y f ▷ N).val.app W
        (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
          (dpDifferentialsSheaf T Y f) N W ω x) =
      Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
        (firstOrderThickeningUnitRestriction T Y f) N W
        ((firstOrderThickeningInrSheaf T Y f).val.app W ω) x := by
    have hmap := Stacks.RingedSpace.tensorSheaf_map_unit_tmul T.scheme.toRingedSpace
      (firstOrderThickeningInrSheaf T Y f) (𝟙 N) W ω x
    exact Eq.trans (PresheafOfModules.hom_congr_apply
      (congrArg (fun k => SheafOfModules.Hom.val k)
        ((Stacks.SheafOfModules.Tensor.sheafTensor_map_app T.scheme.toRingedSpace.sheaf
            (firstOrderThickeningInrSheaf T Y f) N).trans
          (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map T.scheme.toRingedSpace.sheaf
            (firstOrderThickeningInrSheaf T Y f) (𝟙 N)).symm)) W _) hmap
  have b2 : (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
          (firstOrderThickeningProjHom T Y f)
          (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N).val.app W
        (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
          (firstOrderThickeningUnitRestriction T Y f) N W
          ((firstOrderThickeningInrSheaf T Y f).val.app W ω) x) =
      Stacks.PullbackTensorCoherence.tmul (firstOrderThickeningScheme T Y f).toRingedSpace
        (schemeUnitModule (firstOrderThickeningScheme T Y f))
        ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)
        ((RingedSpaceModuleAdjunction.opensMap
          (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)
        (firstOrderIdealScalar T Y f W ω)
        (Stacks.RingedSpace.pullbackUnit
          (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W x) := a2
  change (λ_ ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)).hom.val.app
      ((RingedSpaceModuleAdjunction.opensMap
        (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)
      ((Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
          (firstOrderThickeningProjHom T Y f)
          (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N).val.app W
        ((firstOrderThickeningInrSheaf T Y f ▷ N).val.app W
          (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
            (dpDifferentialsSheaf T Y f) N W ω x))) = _
  rw [b1, b2, a3]
  rfl

/-- **The canonical map of [Stacks, Tag 07J6] is the symmetry constraint followed by the
braiding-free composite.**  `Crystalline.firstOrderThickeningProjectionFormulaMap` begins with
the symmetry constraint, and by naturality of the braiding that constraint moves to the front of
the whole composite, where it can be cancelled against an isomorphism. -/
theorem whiskerLeft_inrSheaf_comp_firstOrderThickeningProjectionFormulaMap :
    (N ◁ firstOrderThickeningInrSheaf T Y f) ≫
        firstOrderThickeningProjectionFormulaMap T Y f N =
      (β_ N (dpDifferentialsSheaf T Y f)).hom ≫ firstOrderBraidedProjectionFormula T Y f N := by
  have h1 : (N ◁ firstOrderThickeningInrSheaf T Y f) ≫
        (β_ N (firstOrderThickeningUnitRestriction T Y f)).hom =
      (β_ N (dpDifferentialsSheaf T Y f)).hom ≫ (firstOrderThickeningInrSheaf T Y f ▷ N) :=
    BraidedCategory.braiding_naturality_right N (firstOrderThickeningInrSheaf T Y f)
  change (N ◁ firstOrderThickeningInrSheaf T Y f) ≫
      (β_ N (firstOrderThickeningUnitRestriction T Y f)).hom ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
            (firstOrderThickeningProjHom T Y f)
            (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N ≫
          (Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).map
            (λ_ ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)).hom = _
  rw [← Category.assoc, h1, Category.assoc]
  rfl

end Crystalline

end

end
