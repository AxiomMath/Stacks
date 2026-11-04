module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftTensorPresheaf

/-!
# Global presentations restrict along arrows of the site

Global presentations restrict along arrows of the site, stated at the objects of the restriction
functor.

## Main results

* `hasGlobalPresentation_overMap_obj_globalPresentationOverMapObj`: if a sheaf of modules on the
  slice over `Y` has a global presentation, so does its restriction along `f : X ⟶ Y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace Stacks.SheafOfModules.GlobalPresentationTransport

section Restriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A global presentation restricts along an arrow of the site**, for any module on the
larger slice. -/
theorem hasGlobalPresentation_overMap_obj_globalPresentationOverMapObj {X Y : C} (f : X ⟶ Y)
    (P : SheafOfModules.{w} (R.over Y)) (h : P.HasGlobalPresentation) :
    ((SheafOfModules.overMap.{w} R f).obj P).HasGlobalPresentation := by
  have h1 (Z : C) : HasSheafify (J.over Z) AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over Z)
  have h2 (Z : C) : (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} (J.over Z)
  have hF : PreservesColimitsOfSize.{max u v w, max u v w}
      (SheafOfModules.overMap.{max u v w} R f) :=
    Stacks.SheafOfModules.overMap_preservesColimits.{u, v, max u v w, w} R f
  have hF₀ : (SheafOfModules.overMap.{max u v w} R f).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have hη₁ : (SheafOfModules.overMap.{max u v w} R f).obj
      (SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (SheafOfModules.unit (R.over Y))) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (SheafOfModules.unit (R.over X)) :=
    pushforwardUliftIso.{max u v, v, w, max u v w} (Sheaf.pushforwardOverMapIso R f).inv
        (SheafOfModules.unit (R.over Y)) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{max u v, v, w, w, max u v w}
        (SheafOfModules.overMapUnitIso f)
  have hηM : (SheafOfModules.overMap.{max u v w} R f).obj
      (SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w} P) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        ((SheafOfModules.overMap.{w} R f).obj P) :=
    pushforwardUliftIso.{max u v, v, w, max u v w} (Sheaf.pushforwardOverMapIso R f).inv P
  exact hasGlobalPresentation_of_functor.{max u v, v, w} P
    (F₀ := SheafOfModules.overMap.{w} R f)
    (F := SheafOfModules.overMap.{max u v w} R f) hF hF₀ hη₁ hηM h

end Restriction

end Stacks.SheafOfModules.GlobalPresentationTransport

end
