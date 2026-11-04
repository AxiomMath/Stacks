module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparison

/-!
# The comparison maps of restricted modules compose

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `φ : x ⟶ y` and
`ψ : y ⟶ z` be arrows of `𝒳`, lying over morphisms of schemes `a : U ⟶ V` and `b : V ⟶ W`. The
comparison maps along `φ`, `ψ` and `ψ ∘ φ` of the restriction of a presheaf to the small étale
sites compose, up to the identification of the base change along `b ∘ a` with the two successive
base changes. This file proves the same for the map `a_{small}^♯` of structure sheaves and for the
comparison of a presheaf of modules, on sections.

## Main results

* `AlgebraicGeometry.Stack.smallEtaleStructureComparison_app_comp`: the maps `a_{small}^♯` of
  structure sheaves compose.
* `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_comp`: the direct-image
  comparison for a presheaf of modules composes.

## References

* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)

/-- The canonical identification between the base change along the morphism of schemes below
`ψ ∘ φ` and the two successive base changes, for arrows `φ : x ⟶ y` and `ψ : y ⟶ z` of `𝒳`. -/
noncomputable abbrev smallEtaleBaseChangeCompIso :=
  smallEtaleBaseChange_factoredCompIso E _ _ _
    (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
    (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
    (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm

/-- The map `a_{small}^♯` of structure sheaves below `φ`, applied after the map `b_{small}^♯`
below `ψ`, is the map below `ψ ∘ φ` followed by restriction along the identification of the two
base changes. -/
@[stacks 075D "part (1), for the maps of structure sheaves below an arrow"]
theorem smallEtaleStructureComparison_app_comp
    (W : (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))ᵒᵖ)
    (r : (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj.obj W) :
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).op.obj W)
        ((smallEtaleStructureComparison B E h S hS p hp ψ τ hτ).app W r) =
      (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj.map
        ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).hom.app W.unop).op
        ((smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ).app W r) := by
  induction W with | op W => ?_
  have hcancel := ConcreteCategory.congr_hom
    ((localStructurePresheafIso B E h S hS p hp y τ hτ).inv_hom_id_app
      (Opposite.op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj W)))
  have hcomp := ConcreteCategory.congr_hom
    (restrictionPushforwardComparison_app_comp B E h S hS p hp φ ψ
      (ringStructureSheafCore B S hS p hp τ hτ).obj W)
    ((localStructurePresheafIso B E h S hS p hp z τ hτ).hom.app (Opposite.op W) r)
  have hnat := ConcreteCategory.congr_hom
    ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.naturality
      ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).hom.app W).op)
    ((restrictionPushforwardComparison B E h S hS p hp (φ ≫ ψ)
        (ringStructureSheafCore B S hS p hp τ hτ).obj).app (Opposite.op W)
      ((localStructurePresheafIso B E h S hS p hp z τ hτ).hom.app (Opposite.op W) r))
  simp only [smallEtaleStructureComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.op_obj, CategoryTheory.comp_apply, CategoryTheory.id_apply] at hcancel hcomp hnat ⊢
  rwa [hcancel, hcomp]

/-- The direct-image comparison of a presheaf of modules below `φ`, applied after the
comparison below `ψ`, is the comparison below `ψ ∘ φ` followed by restriction along the
identification of the two base changes. -/
@[stacks 075D "part (1), for the direct-image comparison of a presheaf of modules"]
theorem restrictModulePushforwardComparison_app_comp
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (W : (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))ᵒᵖ)
    (n : (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F).obj W) :
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F).app
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).op.obj W)
        ((restrictModulePushforwardComparison B E h S hS p hp ψ τ hτ F).app W n) =
      (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).presheaf.map
        ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).hom.app W.unop).op
        ((restrictModulePushforwardComparison B E h S hS p hp (φ ≫ ψ) τ hτ F).app W n) := by
  induction W with | op W => ?_
  exact ConcreteCategory.congr_hom
    (restrictionPushforwardComparison_app_comp B E h S hS p hp φ ψ F.presheaf W) n

end AlgebraicGeometry.Stack

end
