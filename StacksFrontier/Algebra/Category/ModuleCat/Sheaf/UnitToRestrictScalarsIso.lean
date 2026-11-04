module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf

/-!
# When the unit map to a restriction of scalars is an isomorphism

For a morphism `α : R ⟶ R'` of sheaves of rings, the morphism of `R`-modules
`SheafOfModules.unitToRestrictScalarsObjUnit α : R ⟶ α_* R'` is sectionwise `α` itself. So it is
an isomorphism exactly when `α` is, and it vanishes exactly when every component of `α` does.

## Main results

* `SheafOfModules.isIso_of_isIso_unitToRestrictScalarsObjUnit`
* `SheafOfModules.isIso_unitToRestrictScalarsObjUnit_of_isIso`
* `SheafOfModules.app_eq_zero_of_unitToRestrictScalarsObjUnit_eq_zero`
-/

@[expose] public noncomputable section

open CategoryTheory

universe u u' v'

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- If `R ⟶ α_* R'` is an isomorphism, every component of `α` is bijective. -/
theorem bijective_app_of_isIso_unitToRestrictScalarsObjUnit
    [IsIso (unitToRestrictScalarsObjUnit α)] (U : Cᵒᵖ) :
    Function.Bijective (α.hom.app U) := by
  have h : IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U).map
      (unitToRestrictScalarsObjUnit α)) := Functor.map_isIso _ _
  exact (ConcreteCategory.bijective_of_isIso _ : Function.Bijective
    ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U).map
      (unitToRestrictScalarsObjUnit α)))

/-- If `R ⟶ α_* R'` is an isomorphism of `R`-modules, then `α` is an isomorphism. -/
theorem isIso_of_isIso_unitToRestrictScalarsObjUnit
    [IsIso (unitToRestrictScalarsObjUnit α)] : IsIso α := by
  have : ∀ U, IsIso (α.hom.app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_app_of_isIso_unitToRestrictScalarsObjUnit α U)
  have : IsIso ((sheafToPresheaf J RingCat.{u}).map α) := NatIso.isIso_of_isIso_app (α.hom)
  exact isIso_of_reflects_iso α (sheafToPresheaf J RingCat.{u})

/-- If `α` is an isomorphism, so is `R ⟶ α_* R'`. -/
theorem isIso_unitToRestrictScalarsObjUnit_of_isIso [IsIso α] :
    IsIso (unitToRestrictScalarsObjUnit α) := by
  have : IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map
      (unitToRestrictScalarsObjUnit α)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    have : IsIso (α.hom.app U) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso (α.hom.app U) :)
  exact isIso_of_reflects_iso _ (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)

/-- If `R ⟶ α_* R'` vanishes, so does every component of `α`. -/
theorem app_eq_zero_of_unitToRestrictScalarsObjUnit_eq_zero
    (h : unitToRestrictScalarsObjUnit α = 0) (U : Cᵒᵖ) (a : R.obj.obj U) :
    α.hom.app U a = 0 := by
  have := congrArg (fun g => PresheafOfModules.Hom.app g.val U a) h
  exact this

end SheafOfModules
