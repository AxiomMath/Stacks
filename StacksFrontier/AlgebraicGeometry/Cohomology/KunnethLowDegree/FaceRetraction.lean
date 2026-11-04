module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.Edge

/-!
# A retraction of the face map of a section

Let `i : X ⟶ W` and `π : W ⟶ X` be morphisms of schemes with `i ≫ π = 𝟙 X`, for instance a
face `X ≅ X × {y₀} ⊆ X × Y` and the projection. The composite

`𝒪_X ⟶ π_* 𝒪_W ⟶ π_* i_* i^* 𝒪_W`

of the structure map of `π` with `π_*` of the unit of `i^* ⊣ i_*` has a retraction, made of the
counit-side map `i^* 𝒪_W ⟶ 𝒪_X` and the identifications `π_* i_* = (i ≫ π)_* = 𝟙_* = 𝟙`. On
cohomology this composite is therefore injective.

## Main definitions

* `Stacks.KunnethLowDegree.faceRetraction`: the retraction.

## Main results

* `Stacks.KunnethLowDegree.faceSection_comp_faceRetraction`: it is a retraction.
* `Stacks.KunnethLowDegree.injective_H_faceSection`: injectivity on cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.KunnethLowDegree

variable {X W : Scheme.{u}} (i : X ⟶ W) (π : W ⟶ X)

/-- The direct image of sheaves of modules along a morphism of schemes, in the spelling of
`SheafOfModules.pushforward`, is a right adjoint. -/
local instance isRightAdjoint_pushforward {A B : Scheme.{u}} (f : A ⟶ B) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

/-- The composite `𝒪_X ⟶ π_* 𝒪_W ⟶ π_* i_* i^* 𝒪_W`, for any `i : Z ⟶ W`. -/
def faceSection {Z : Scheme.{u}} (i : Z ⟶ W) : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.pushforward π).obj ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj (SheafOfModules.unit W.ringCatSheaf))) :=
  SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫
    (Scheme.Modules.pushforward π).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (SheafOfModules.unit W.ringCatSheaf))

/-- The retraction `π_* i_* i^* 𝒪_W ⟶ 𝒪_X` of `faceSection`, when `i ≫ π = 𝟙 X`. -/
def faceRetraction (h : i ≫ π = 𝟙 X) :
    (Scheme.Modules.pushforward π).obj ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj (SheafOfModules.unit W.ringCatSheaf))) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pushforward π).map ((Scheme.Modules.pushforward i).map
      (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom)) ≫
    (Scheme.Modules.pushforwardComp i π).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr h).hom.app _ ≫
    (Scheme.Modules.pushforwardId X).hom.app _

/-- The unit of `i^* ⊣ i_*` at `𝒪_W`, followed by `i_*` of `i^* 𝒪_W ⟶ 𝒪_X`, is the structure
map `𝒪_W ⟶ i_* 𝒪_X`. -/
theorem unit_comp_pushforward_pullbackObjUnitToUnit :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (SheafOfModules.unit W.ringCatSheaf) ≫
      (Scheme.Modules.pushforward i).map
        (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)

/-- **`faceRetraction` is a retraction of `faceSection`.** -/
theorem faceSection_comp_faceRetraction (h : i ≫ π = 𝟙 X) :
    faceSection π i ≫ faceRetraction i π h = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  have hU : U = i ⁻¹ᵁ π ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.id_preimage]
  ext a
  change X.presheaf.map (eqToHom hU).op (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SheafOfModules.unit W.ringCatSheaf) ≫
        (Scheme.Modules.pushforward i).map
          (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom)) (π ⁻¹ᵁ U)
      (π.app U a)) = a
  rw [congrArg (fun f => Scheme.Modules.Hom.app f (π ⁻¹ᵁ U))
    (unit_comp_pushforward_pullbackObjUnitToUnit i)]
  change X.presheaf.map (eqToHom hU).op (i.app (π ⁻¹ᵁ U) (π.app U a)) = a
  have hc := Scheme.Hom.congr_app h U
  rw [Scheme.Hom.comp_app] at hc
  have hring : π.app U ≫ i.app (π ⁻¹ᵁ U) ≫ X.presheaf.map (eqToHom hU).op = 𝟙 _ := by
    rw [← Category.assoc, hc, Scheme.Hom.id_app]
    exact (Category.assoc _ _ _).trans ((Category.id_comp _).trans
      ((X.presheaf.map_comp _ _).symm.trans
        ((congrArg X.presheaf.map (Subsingleton.elim _ (𝟙 _))).trans (X.presheaf.map_id _))))
  exact congrArg (fun g => g.hom a) hring

/-- **On cohomology, `faceSection` is injective.** -/
theorem injective_H_faceSection (h : i ≫ π = 𝟙 X) (n : ℕ) :
    Function.Injective (((moduleGlobalSections X).rightDerived n).map (faceSection π i)).hom := by
  have e : ((moduleGlobalSections X).rightDerived n).map (faceSection π i) ≫
      ((moduleGlobalSections X).rightDerived n).map (faceRetraction i π h) = 𝟙 _ :=
    (((moduleGlobalSections X).rightDerived n).map_comp _ _).symm.trans
      ((congrArg ((moduleGlobalSections X).rightDerived n).map
        (faceSection_comp_faceRetraction i π h)).trans
        (((moduleGlobalSections X).rightDerived n).map_id _))
  intro a b hab
  have := congrArg (((moduleGlobalSections X).rightDerived n).map (faceRetraction i π h)).hom hab
  rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, e, ModuleCat.id_apply,
    ModuleCat.id_apply] at this

end Stacks.KunnethLowDegree

end
