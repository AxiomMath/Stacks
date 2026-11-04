module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.DegreeZeroBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitDirectImageConeShift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelCocyclePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricFibreBaseChangeSections

/-!
# Stacks 0EYM in degree zero: the comparison with the underived maps

The maps `ψ_{i'i}` and `ψ_i` of [Stacks, Tag 0EYM]
(`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap`,
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap`) are built from the base change map
on higher direct images. In degree zero, through the identification
`Stacks.EtaleCohomology.smallEtaleRightDerivedZeroIso` of `R^0 g_*` with `g_*`, they are the
base change map of the underived direct image followed by `g_*` of the map of sheaves, by
`Stacks.EtaleCohomology.higherBaseChangeMapAb_zero`; and that composite is, transposed, `g_{i, *}`
of the transposed map followed by the identification of the two iterated direct images around the
square. This file records these identities, which carry the degree-zero colimit assertion in
adjoint form (`Colimits/LimitDirectImageDegreeZeroColimit.lean`) to the colimit assertion for the
maps `ψ` (`Colimits/LimitHigherDirectImageColimitAssertion.lean`).

## Main results

* `Stacks.EtaleCohomology.homEquiv_smallEtaleBaseChangeAb_app_comp` — the transpose of the base
  change map of a square followed by a direct image.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap_ab_eq` — the degree-zero transition
  maps of `Colimits/LimitDirectImageSystem.lean` are the base change map followed by `g_{i', *}φ`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap_ab_comp_rightDerivedZeroIso` and
  `Stacks.EtaleCohomology.LimitHigherDirectImage.rightDerivedZeroIso_comp_projectionMap` — the maps
  `ψ` in degree zero, through `R^0 g_* = g_*`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap_zero_comp_iff` — the factorisation
  condition of the colimit assertion in degree zero, transposed.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open Stacks.EtaleCohomology.LimitDirectImage

universe v u


namespace Stacks.EtaleCohomology

section Square

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The transpose of the base change map followed by a direct image.** For a commutative square
and `φ : e^{-1}M ⟶ N`, the transpose under the adjunction for `f'` of `BC_M ≫ h_*φ` is `g_*` of
the transpose of `φ` under the adjunction for `e`, followed by the identification of the two
iterated direct images. -/
theorem homEquiv_smallEtaleBaseChangeAb_app_comp (M : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (N : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (φ : (smallEtalePullbackAb e).obj M ⟶ N) :
    (smallEtaleAdjunctionAb f').homEquiv _ _
        ((smallEtaleBaseChangeAb f' g h e w).app M ≫ (smallEtalePushforwardAb h).map φ) =
      (smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).homEquiv _ _ φ) ≫
        (smallEtaleSquarePushforwardIso f' g h e w).hom.app N := by
  have hnat := (smallEtaleSquarePushforwardIso f' g h e w).hom.naturality φ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have hu := unit_comp_smallEtaleBaseChangeAb_app f' g h e w M
  rw [← smallEtaleSquarePushforwardIso_eq f' g h e w] at hu
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    ← Category.assoc, hu, Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp]

end Square

namespace LimitHigherDirectImage

section Generic

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)

/-- **The degree-zero transition maps are the base change map followed by `g_{i', *}φ`.** The map
`Stacks.EtaleCohomology.LimitDirectImage.transitionMap` is defined as a transpose; this is the
source's description of it, the one through which it is compared with the transition maps
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap` on higher direct images. -/
theorem transitionMap_ab_eq (F : EtaleSheafSystem DX Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    LimitDirectImage.transitionMap γ Ab.{u + 1} F a =
      (smallEtaleBaseChangeAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
          (transition_comm γ a)).app (F.obj j) ≫
        (smallEtalePushforwardAb (γ.app i)).map (F.map a) := by
  apply ((systemAdjunction DS Ab.{u + 1} a).homEquiv _ _).injective
  refine (LimitDirectImage.transitionMap_transpose γ Ab.{u + 1} F a).trans ?_
  exact (homEquiv_smallEtaleBaseChangeAb_app_comp (DS.map a) (γ.app j) (γ.app i) (DX.map a)
    (transition_comm γ a) (F.obj j) (F.obj i) (F.map a)).symm

/-- The degree-zero base change map on higher direct images, through `R^0 = g_*`, followed by
`R^0 h_*φ` is the underived base change map followed by `h_*φ`. -/
private theorem pullback_map_comp_higherBaseChangeMapAb_zero_comp_map
    {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
    (w : h ≫ f' = e ≫ g) (M : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (N : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (φ : (smallEtalePullbackAb e).obj M ⟶ N) :
    (smallEtalePullbackAb f').map ((smallEtaleRightDerivedZeroIso g).hom.app M) ≫
        (higherBaseChangeMapAb f' g h e w 0).app M ≫ (smallEtaleRightDerivedZero h).map φ =
      (smallEtaleBaseChangeAb f' g h e w).app M ≫ (smallEtalePushforwardAb h).map φ ≫
        (smallEtaleRightDerivedZeroIso h).hom.app N := by
  rw [← Category.assoc, higherBaseChangeMapAb_zero, Category.assoc,
    ← (smallEtaleRightDerivedZeroIso h).hom.naturality φ]

/-- **The degree-zero transition maps on higher direct images**, through `R^0 g_{i, *} = g_{i, *}`:
the transition map of `Stacks.EtaleCohomology.LimitDirectImage.transitionMap` followed by the
identification at `i'` is the identification at `i` followed by the transition map
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap` in degree zero. -/
theorem transitionMap_ab_comp_rightDerivedZeroIso (F : EtaleSheafSystem DX Ab.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    LimitDirectImage.transitionMap γ Ab.{u + 1} F a ≫
        (smallEtaleRightDerivedZeroIso (γ.app i)).hom.app (F.obj i) =
      (smallEtalePullbackAb (DS.map a)).map
          ((smallEtaleRightDerivedZeroIso (γ.app j)).hom.app (F.obj j)) ≫
        transitionMap γ 0 F a := by
  rw [transitionMap_ab_eq]
  exact (Category.assoc _ _ _).trans
    (pullback_map_comp_higherBaseChangeMapAb_zero_comp_map (DS.map a) (γ.app j) (γ.app i)
      (DX.map a) (transition_comm γ a) (F.obj j) (F.obj i) (F.map a)).symm

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) (F : EtaleSheafSystem DX Ab.{u + 1})
  (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)

/-- **The degree-zero cocone maps on higher direct images**, through `R^0 g_{i, *} = g_{i, *}` and
`R^0 g_* = g_*`: the base change map of the projection square followed by `g_*ι_i`. -/
theorem rightDerivedZeroIso_comp_projectionMap (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cS.π.app i)).map
          ((smallEtaleRightDerivedZeroIso (γ.app i)).hom.app (F.obj i)) ≫
        projectionMap γ cX cS hcS 0 𝓕 F ι i =
      (smallEtaleBaseChangeAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS) (cX.π.app i)
          (limitMorphism_comp_π γ cX cS hcS i)).app (F.obj i) ≫
        (smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).map (ι i) ≫
          (smallEtaleRightDerivedZeroIso (limitMorphism γ cX cS hcS)).hom.app 𝓕 := by
  exact pullback_map_comp_higherBaseChangeMapAb_zero_comp_map (cS.π.app i) (γ.app i)
    (limitMorphism γ cX cS hcS) (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) (F.obj i) 𝓕
    (ι i)

/-- **The factorisation condition of the colimit assertion in degree zero, transposed.** A map
`R^0 g_* 𝓕 ⟶ 𝒢` written as `χ'` after the identification `R^0 g_* = g_*` satisfies
`ψ_i ≫ χ = τ_i` exactly when the transposed cocone map followed by `h_{i, *}χ'` is the transpose of
`τ_i` read on `g_{i, *}F_i`. -/
theorem projectionMap_zero_comp_iff (i : Iᵒᵖ) {𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{u + 1}}
    (τ : (smallEtalePullbackAb (cS.π.app i)).obj
      ((smallEtaleRightDerivedZero (γ.app i)).obj (F.obj i)) ⟶ 𝒢)
    (χ' : (smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).obj 𝓕 ⟶ 𝒢) :
    projectionMap γ cX cS hcS 0 𝓕 F ι i ≫
          ((smallEtaleRightDerivedZeroIso (limitMorphism γ cX cS hcS)).inv.app 𝓕 ≫ χ' :
            (smallEtaleRightDerivedZero (limitMorphism γ cX cS hcS)).obj 𝓕 ⟶ 𝒢) = τ ↔
      projectionTranspose γ Ab.{u + 1} cX cS hcS F (systemDirLeg cX F 𝓕 ι) i ≫
          (smallEtalePushforwardAb (cS.π.app i)).map χ' =
        (smallEtaleAdjunctionAb (cS.π.app i)).homEquiv
          ((smallEtalePushforwardAb (γ.app i)).obj (F.obj i)) 𝒢
          ((smallEtalePullbackAb (cS.π.app i)).map
            ((smallEtaleRightDerivedZeroIso (γ.app i)).hom.app (F.obj i)) ≫ τ) := by
  rw [← cancel_epi ((smallEtalePullbackAb (cS.π.app i)).map
    ((smallEtaleRightDerivedZeroIso (γ.app i)).hom.app (F.obj i))), ← Category.assoc,
    rightDerivedZeroIso_comp_projectionMap, Category.assoc, Category.assoc,
    Iso.hom_inv_id_app_assoc, ← Equiv.apply_eq_iff_eq
      ((smallEtaleAdjunctionAb (cS.π.app i)).homEquiv _ _), ← Category.assoc,
    Adjunction.homEquiv_naturality_right, homEquiv_smallEtaleBaseChangeAb_app_comp]
  rfl

end Generic


end LimitHigherDirectImage

end Stacks.EtaleCohomology

end
