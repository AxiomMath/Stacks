module

public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSheafMap
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.CategoryTheory.Limits.TerminalGlobalSectionMap

/-!
# The map `(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` on inverse images of global sections

For morphisms of algebraic spaces `u : W ⟶ X` and `h : X ⟶ Y`, the map
`AlgebraicGeometry.Space.inverseImageStructureSheafMap` carries the inverse image along `u ≫ h` of
a global section `t` of `𝒪_Y` to the inverse image along `u` of the global section `h^♯(h⁻¹t)` of
`𝒪_X`, on underlying sheaves of sets. This is how the algebra structure of the extension of a
first-order thickening (Stacks 0D1K) is read on the functions of the base.

## Main results

* `AlgebraicGeometry.Space.globalSectionMap_comp_forget_map_inverseImageStructureSheafMap`

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W X Y : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits in presheaves on the small étale site
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_discrete_InverseImageStructureSheafMapGlobalSection
    (Z : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of sheaves of sets on the small étale site
/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_InverseImageStructureSheafMapGlobalSection
    (Z : AlgebraicSpaces B S hS) : HasTerminal (smallEtaleRingedTopos B S hS Z).Topos :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1})
      ((SmallEtale B S hS Z.1)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type u))

set_option maxHeartbeats 800000 in
-- elaborating the composite `sheafCompose` and topos inverse-image terms of the proof
set_option synthInstance.maxHeartbeats 400000 in
/-- **The map `(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` on inverse images of global sections.** For a global
section `t` of `𝒪_Y` (a morphism from the terminal sheaf of sets), the inverse image of `t` along
`u ≫ h` is carried to the inverse image along `u` of the global section of `𝒪_X` obtained from
the inverse image of `t` along `h` by the structure map `h^♯ : h⁻¹𝒪_Y ⟶ 𝒪_X`. -/
theorem globalSectionMap_comp_forget_map_inverseImageStructureSheafMap (u : W ⟶ X) (h : X ⟶ Y)
    (t : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS Y).O) :
    (smallEtaleRingedToposHom B S hS (u ≫ h)).toToposHom.inverseImage.globalSectionMap t ≫
        (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
          (inverseImageStructureSheafMap B S hS u h) =
      (smallEtaleRingedToposHom B S hS u).toToposHom.inverseImage.globalSectionMap
        ((smallEtaleRingedToposHom B S hS h).toToposHom.inverseImage.globalSectionMap t ≫
          (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
            (smallEtaleRingedToposHom B S hS h).fSharpInverseImage) := by
  have hc : (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS u h).inv.app
        (smallEtaleRingedTopos B S hS Y).O) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS u h).inv.app _ := by
    rw [smallEtaleRingedToposHom_compInverseImageRingIso, Iso.trans_inv, NatTrans.comp_app,
      Functor.map_comp]
    exact (congrArg (_ ≫ ·)
      (Stacks.Sheaves.ToposPushforward.forget_map_inverseImageCommRingComp_inv
        (smallEtaleRingedToposHom B S hS h).toToposHom
        (smallEtaleRingedToposHom B S hS u).toToposHom
        (smallEtaleRingedTopos B S hS Y).O)).trans (Category.comp_id _)
  have hm : (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
      (inverseImageStructureSheafMap B S hS u h) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS u h).inv.app _ ≫
        (smallEtaleRingedToposHom B S hS u).toToposHom.inverseImage.map
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
            (smallEtaleRingedToposHom B S hS h).fSharpInverseImage) :=
    ((sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map_comp _ _).trans
      ((congrArg (· ≫ _) hc).trans (congrArg (_ ≫ ·)
        (Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
          (SmallEtale.topology B S hS W.1)
          (Φ := (smallEtaleRingedToposHom B S hS u).toToposHom.inverseImage)
          (smallEtaleRingedToposHom B S hS h).fSharpInverseImage)))
  refine (congrArg (_ ≫ ·) hm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Functor.globalSectionMap_comp_inv_app
    (F := (smallEtaleRingedToposHom B S hS h).toToposHom.inverseImage)
    (G := (smallEtaleRingedToposHom B S hS u).toToposHom.inverseImage)
    (smallEtaleRingedToposHom_compInverseImageIso B S hS u h) t)).trans ?_
  exact Functor.globalSectionMap_comp _ _ _

end AlgebraicGeometry.Space

end
