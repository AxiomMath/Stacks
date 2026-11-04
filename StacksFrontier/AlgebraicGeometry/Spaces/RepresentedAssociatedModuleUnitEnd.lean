module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedModuleStalk

/-!
# `ε^*` on endomorphisms of the structure sheaf of a represented algebraic space

Let `U` be an object of the big fppf site over `S`, with scheme `T`, and let
`ε^* = AlgebraicGeometry.Space.representedAssociatedModule` be the associated-module functor of
Stacks 03DU (4) from `𝒪_T`-modules to modules on the small étale site of `yoneda.obj U`.  It
carries `𝒪_T` to `𝒪` (`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`), so it
carries an endomorphism `t` of `𝒪_T` to an endomorphism of `𝒪`.  This file computes the latter
over the identity chart: it takes `1` to the global function `t(1)` of `T`.

## Main results

* `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso_conj_val_app_selfChart`:
  **`ε^*t`, read on `𝒪` through `representedAssociatedModuleObjUnitIso`, takes the section `1`
  over the identity chart to `t(1)`.**

## Implementation notes

This is `AlgebraicGeometry.Space.representedAffineUnitIso_conj_val_app_one` without the
restriction along an isomorphism `T ≅ Spec A` and for an arbitrary endomorphism `t`; the proof
is the same three steps: the pushforward along the equivalence of small étale sites is the
identity on sections, the transpose of `SheafOfModules.pullbackObjUnitToUnit` evaluates
`t(1)` over the image of `⊤`
(`AlgebraicGeometry.Space.pullbackObjUnitToUnit_conj_val_app_one`), and the restriction of that
image to the identity chart is the identity of `Γ(T, ⊤)`
(`AlgebraicGeometry.Space.structureSheaf_map_structureMap_app_top`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **`ε^*` of an endomorphism `t` of `𝒪_T`, read on `𝒪` through
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`, takes the section `1` over the
identity chart of `yoneda.obj U` to the global function `t(1)` of `T`.** -/
theorem representedAssociatedModuleObjUnitIso_conj_val_app_selfChart
    (t : SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⟶
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) :
    ((representedAssociatedModuleObjUnitIso B S hS U (isAlgebraicSpace_yoneda B S hS U)).inv ≫
        (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map t ≫
          (representedAssociatedModuleObjUnitIso B S hS U
            (isAlgebraicSpace_yoneda B S hS U)).hom).val.app
        (Opposite.op (selfChart B S hS U)) (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) =
      t.val.app (Opposite.op ⊤) (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) := by
  let φ := _root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
  let Y := (representedSmallEtaleEquivalence B S hS U).functor.obj (selfChart B S hS U)
  let c := inv (SheafOfModules.pullbackObjUnitToUnit φ) ≫ (SheafOfModules.pullback φ).map t ≫
      SheafOfModules.pullbackObjUnitToUnit φ
  have hc : ∀ z, ((representedAssociatedModuleObjUnitIso B S hS U
        (isAlgebraicSpace_yoneda B S hS U)).inv ≫
        (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map t ≫
          (representedAssociatedModuleObjUnitIso B S hS U
            (isAlgebraicSpace_yoneda B S hS U)).hom).val.app
        (Opposite.op (selfChart B S hS U)) z = c.val.app (Opposite.op Y) z := fun _ => rfl
  refine (hc (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).trans ?_
  let g : Y ⟶ _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤ :=
    _root_.AlgebraicGeometry.SmallEtale.homOfRangeLe _ _ _ ⊤ (by simp)
  have hnat := congrArg (fun f => f (1 : (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.obj
        (Opposite.op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤))))
    (congrArg ModuleCat.Hom.hom (c.val.naturality g.op))
  simp only [ModuleCat.hom_comp] at hnat
  have h1 := map_one ((_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
        g.op).hom
  have s3 := pullbackObjUnitToUnit_conj_val_app_one φ t (Opposite.op ⊤)
  have hz := structureSheaf_map_structureMap_app_top B S hS U g
    (t.val.app (Opposite.op ⊤) (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
  refine (congrArg (fun y => c.val.app (Opposite.op Y) y) h1).symm.trans ?_
  refine hnat.trans ?_
  refine Eq.trans ?_ hz
  exact congrArg (fun y => ((_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
        g.op) y) s3

end AlgebraicGeometry.Space

end
