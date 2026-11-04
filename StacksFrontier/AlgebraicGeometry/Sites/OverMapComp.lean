module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Restriction of sheaves of modules along an arrow of a site is functorial

For a site `(C, J)` carrying a sheaf of rings `R`, restriction of sheaves of `R`-modules along an
arrow `f : V ⟶ U` of `C` is `SheafOfModules.overMap R f`, the pushforward along
`CategoryTheory.Over.map f`. Restricting along `f` and then along `g : W ⟶ V` is isomorphic to
restricting along `g ≫ f`; this is the sheaf-of-modules form of `CategoryTheory.Over.mapComp`.

## Main definitions

* `Stacks.SheafOfModules.overMapCompIso`: restricting sheaves of modules along `f : V ⟶ U` and
  then along `g : W ⟶ V` is restricting along `g ≫ f`.

## Implementation notes

The ring universe `w` is the first universe parameter, so that `overMapCompIso.{u}` is the
comparison for a sheaf of rings with sections in `Type u`.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- Restricting sheaves of modules along `f : V ⟶ U` and then along `g : W ⟶ V` is isomorphic
to restricting along `g ≫ f`. -/
public noncomputable def overMapCompIso {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    SheafOfModules.overMap.{w} R f ⋙ SheafOfModules.overMap.{w} R g ≅
      SheafOfModules.overMap.{w} R (g ≫ f) := by
  have : (Over.map g ⋙ Over.map f).IsContinuous (J.over W) (J.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over V) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_
  refine SheafOfModules.pushforwardCongr₂ _ (Over.mapComp g f) ?_
  ext A : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have h : ((Functor.sheafPushforwardContinuousNatTrans (Over.mapComp g f).hom RingCat.{w}
      (J.over W) (J.over U)).app (R.over U)).hom.app A = 𝟙 _ := by
    simp; rfl
  rw [h]
  rfl

end Stacks.SheafOfModules

end
