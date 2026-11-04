module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlusPastingHorizontal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.MatePasting

/-!
# Pasting identities for the underived base change maps of étale sheaves of modules

The identities between underived natural transformations of sheaves of `Λ`-modules on small
étale sites that the compatibility of the base change maps for `Rf_!` with composition
([Stacks, Tag 0F7L]) reduces to.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImageComp_assoc_app`: the associativity pentagon of the
  composition isomorphisms of direct images, evaluated at a sheaf.

* `Stacks.EtaleCohomology.etaleModuleBaseChange_pasteV`: the base change map of a composite of
  direct images is the vertical pasting of the base change maps.
* `Stacks.EtaleCohomology.etaleModuleBaseChange_pasteH`: the base change map along a composite of
  inverse images is the horizontal pasting of the base change maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedBaseChangePlus

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ]

/-- **The associativity pentagon of the composition isomorphisms of direct images of sheaves of
modules**, evaluated at a sheaf, with every composite named. -/
theorem etaleModuleDirectImageComp_assoc_app {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) (F : EtaleModules.{u, r} Λ T) :
    (etaleModuleDirectImage.{u, r} Λ h).map
        ((etaleModuleDirectImageComp.{u, r} Λ f g fg hfg).hom.app F) ≫
      (etaleModuleDirectImageComp.{u, r} Λ fg h fgh h₁).hom.app F =
    (etaleModuleDirectImageComp.{u, r} Λ g h gh hgh).hom.app
        ((etaleModuleDirectImage.{u, r} Λ f).obj F) ≫
      (etaleModuleDirectImageComp.{u, r} Λ f gh fgh h₂).hom.app F := by
  have h0 := congrArg (fun z : _ ≅ _ => NatTrans.app z.hom F)
    (smallEtalePushforwardComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂
      (ModuleCat.{max (u + 1) r} Λ))
  simpa [etaleModuleDirectImageComp] using h0

section Vertical

variable {X Y Z X' Y' Z' : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
  (hfg : fg = f ≫ g) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (fg' : X' ⟶ Z') (hfg' : fg' = f' ≫ g')
  (hX : X' ⟶ X) (hY : Y' ⟶ Y) (hZ : Z' ⟶ Z) (w₁ : f' ≫ hY = hX ≫ f) (w₂ : g' ≫ hZ = hY ≫ g)
  (w : fg' ≫ hZ = hX ≫ fg)

/-- **The base change map of a composite of direct images is the vertical pasting of the base
change maps**, read through the composition isomorphisms of direct images. -/
theorem etaleModuleBaseChange_pasteV :
    Functor.whiskerRight (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg).hom
        (etaleModuleInverseImage.{u, r} Λ hZ) ≫
      etaleModuleBaseChange Λ fg fg' hZ hX w =
    pasteV (etaleModuleBaseChange Λ f f' hY hX w₁) (etaleModuleBaseChange Λ g g' hZ hY w₂) ≫
      Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ hX)
        (etaleModuleDirectImageComp.{u, r} Λ f' g' fg' hfg').hom := by
  have hm₁ : fg' ≫ hZ = (f' ≫ hY) ≫ g := by simp only [hfg', Category.assoc, w₂]
  have hm₂ : fg' ≫ hZ = f' ≫ g' ≫ hZ := by rw [hfg', Category.assoc]
  refine Stacks.CategoryTheory.MatePasting.pasteV_eq_of_mateEquiv_symm
    (etaleModuleInverseImageAdj.{u, r} Λ hX) (etaleModuleInverseImageAdj.{u, r} Λ hY)
    (etaleModuleInverseImageAdj.{u, r} Λ hZ) (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg)
    (etaleModuleDirectImageComp.{u, r} Λ f' g' fg' hfg') _ _ _ _ _ _
    (etaleModuleBaseChange_eq_mateEquiv_symm Λ f f' hY hX w₁)
    (etaleModuleBaseChange_eq_mateEquiv_symm Λ g g' hZ hY w₂)
    (etaleModuleBaseChange_eq_mateEquiv_symm Λ fg fg' hZ hX w) fun F => ?_
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  exact Stacks.CategoryTheory.MatePasting.comp_eq_of_pentagons_v
    (etaleModuleDirectImage.{u, r} Λ g) _
    ((etaleModuleDirectImageComp.{u, r} Λ f' hY (f' ≫ hY) rfl).app F) _
    ((etaleModuleDirectImageComp.{u, r} Λ g' hZ (g' ≫ hZ) rfl).app _) _ _ _
    ((etaleModuleDirectImageComp.{u, r} Λ fg' hZ (fg' ≫ hZ) rfl).app F) _ _
    (etaleModuleDirectImageComp_assoc_app Λ hX f g (f' ≫ hY) w₁ fg hfg (fg' ≫ hZ) hm₁ w F)
    (etaleModuleDirectImageComp_assoc_app Λ f' hY g (f' ≫ hY) rfl (g' ≫ hZ) w₂ (fg' ≫ hZ) hm₁
      hm₂ F)
    (etaleModuleDirectImageComp_assoc_app Λ f' g' hZ fg' hfg' (g' ≫ hZ) rfl (fg' ≫ hZ) rfl hm₂
      F)

end Vertical

section Horizontal

variable {X Y X' Y' X'' Y'' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'')
  (g₁ : Y' ⟶ Y) (g₁' : X' ⟶ X) (g₂ : Y'' ⟶ Y') (g₂' : X'' ⟶ X')
  (w₁ : f' ≫ g₁ = g₁' ≫ f) (w₂ : f'' ≫ g₂ = g₂' ≫ f') (w : f'' ≫ (g₂ ≫ g₁) = (g₂' ≫ g₁') ≫ f)

/-- **The base change map along a composite of inverse images is the horizontal pasting of the
base change maps**, read through the composition isomorphisms of inverse images. -/
theorem etaleModuleBaseChange_pasteH :
    pasteH (etaleModuleBaseChange Λ f f' g₁ g₁' w₁) (etaleModuleBaseChange Λ f' f'' g₂ g₂' w₂)
        (etaleModuleInverseImageCompIso.{u, r} Λ g₂ g₁).symm
        (etaleModuleInverseImageCompIso.{u, r} Λ g₂' g₁').symm =
      etaleModuleBaseChange Λ f f'' (g₂ ≫ g₁) (g₂' ≫ g₁') w := by
  have hm₁ : f'' ≫ g₂ ≫ g₁ = (f'' ≫ g₂) ≫ g₁ := (Category.assoc _ _ _).symm
  have hm₂ : f'' ≫ g₂ ≫ g₁ = g₂' ≫ f' ≫ g₁ := by rw [← Category.assoc, w₂, Category.assoc]
  refine Stacks.CategoryTheory.MatePasting.pasteH_eq_of_mateEquiv_symm
    (etaleModuleInverseImageAdj.{u, r} Λ g₁') (etaleModuleInverseImageAdj.{u, r} Λ g₁)
    (etaleModuleInverseImageAdj.{u, r} Λ g₂') (etaleModuleInverseImageAdj.{u, r} Λ g₂)
    (etaleModuleInverseImageAdj.{u, r} Λ (g₂' ≫ g₁'))
    (etaleModuleInverseImageAdj.{u, r} Λ (g₂ ≫ g₁))
    (etaleModuleInverseImageCompIso.{u, r} Λ g₂' g₁').symm
    (etaleModuleInverseImageCompIso.{u, r} Λ g₂ g₁).symm
    (etaleModuleDirectImageComp.{u, r} Λ g₂' g₁' (g₂' ≫ g₁') rfl)
    (etaleModuleDirectImageComp.{u, r} Λ g₂ g₁ (g₂ ≫ g₁) rfl)
    (conjugateEquiv_etaleModuleInverseImageCompIso_inv.{u, r} Λ g₂' g₁')
    (conjugateEquiv_etaleModuleInverseImageCompIso_inv.{u, r} Λ g₂ g₁) _ _ _ _ _ _
    (etaleModuleBaseChange_eq_mateEquiv_symm Λ f f' g₁ g₁' w₁)
    (etaleModuleBaseChange_eq_mateEquiv_symm Λ f' f'' g₂ g₂' w₂)
    (etaleModuleBaseChange_eq_mateEquiv_symm Λ f f'' (g₂ ≫ g₁) (g₂' ≫ g₁') w) fun F => ?_
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  exact Stacks.CategoryTheory.MatePasting.comp_eq_of_pentagons_h
    (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleDirectImage.{u, r} Λ g₁)
    ((etaleModuleDirectImageComp.{u, r} Λ g₂' g₁' (g₂' ≫ g₁') rfl).app F) _
    ((etaleModuleDirectImageComp.{u, r} Λ f' g₁ (f' ≫ g₁) rfl).app _) _
    ((etaleModuleDirectImageComp.{u, r} Λ f'' g₂ (f'' ≫ g₂) rfl).app F) _ _
    ((etaleModuleDirectImageComp.{u, r} Λ f'' (g₂ ≫ g₁) (f'' ≫ g₂ ≫ g₁) rfl).app F) _ _
    (etaleModuleDirectImageComp_assoc_app Λ g₂' g₁' f (g₂' ≫ g₁') rfl (f' ≫ g₁) w₁
      (f'' ≫ g₂ ≫ g₁) w hm₂ F)
    (etaleModuleDirectImageComp_assoc_app Λ g₂' f' g₁ (f'' ≫ g₂) w₂ (f' ≫ g₁) rfl
      (f'' ≫ g₂ ≫ g₁) hm₁ hm₂ F)
    (etaleModuleDirectImageComp_assoc_app Λ f'' g₂ g₁ (f'' ≫ g₂) rfl (g₂ ≫ g₁) rfl
      (f'' ≫ g₂ ≫ g₁) hm₁ rfl F)

end Horizontal

end Stacks.EtaleCohomology
