module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Sheafifying a presheaf of modules that is already a sheaf

The counit of the sheafification adjunction for presheaves of modules is always an isomorphism,
and that is what identifies the sheafification of the presheaf underlying a sheaf of modules with
that sheaf. **This file records the statement about the unit**: if the presheaf of abelian groups
underlying a presheaf of modules is already a sheaf, then the sheafification unit is an
isomorphism, and in particular bijective on the sections over every object.

## Main results

* `PresheafOfModules.isIso_toPresheaf_map_unit_app`: the sheafification unit of a presheaf of
  modules whose underlying presheaf is a sheaf is an isomorphism, after forgetting the module
  structure.
* `PresheafOfModules.bijective_unit_app_app_of_isSheaf`: it is therefore bijective on sections
  over every object, and `PresheafOfModules.unitAppEquiv` packages that as a linear
  equivalence.

The statements are about `(sheafificationAdjunction α).unit.app M` rather than about this
repository's abbreviation `PresheafOfModules.sheafifyUnit` for it, so that this file depends on
Mathlib alone; the abbreviation is reducible, so they apply to it unchanged.

## Implementation notes

The whole content is Mathlib's `CategoryTheory.isIso_toSheafify` together with the fact —
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`, which holds by `rfl` — that
the unit of the module sheafification adjunction *is* `CategoryTheory.toSheafify` after forgetting
the module structure. Invertibility is then read back through
`CategoryTheory.Functor.ReflectsIsomorphisms` for `PresheafOfModules.toPresheaf`.

This is stated and not left to instance search on purpose. `IsIso (sheafifyUnit α M)` is **false**
for a general `M`, so there is no instance to find; the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded` record a proof search that
walked into exactly that goal and failed. The sheaf hypothesis has to be supplied by hand, which
is what these two lemmas are for.
-/

@[expose] public section

open CategoryTheory Limits

universe v u t

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [HasWeakSheafify J AddCommGrpCat.{t}]
  (M : PresheafOfModules.{t} R₀)

/-- **The sheafification unit of a presheaf of modules that is already a sheaf is an
isomorphism**, after forgetting the module structure. This is
`CategoryTheory.isIso_toSheafify`, read through
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`. -/
theorem isIso_toPresheaf_map_unit_app (hM : Presheaf.IsSheaf J M.presheaf) :
    IsIso ((toPresheaf R₀).map ((sheafificationAdjunction α).unit.app M)) := by
  have : IsIso (CategoryTheory.toSheafify J M.presheaf) :=
    CategoryTheory.isIso_toSheafify J hM
  show IsIso (CategoryTheory.toSheafify J M.presheaf)
  infer_instance

/-- **The sheafification unit of a presheaf of modules that is already a sheaf is bijective on
sections over every object.** -/
theorem bijective_unit_app_app_of_isSheaf (hM : Presheaf.IsSheaf J M.presheaf) (U : Cᵒᵖ) :
    Function.Bijective (((sheafificationAdjunction α).unit.app M).app U).hom := by
  have := isIso_toPresheaf_map_unit_app α M hM
  exact ConcreteCategory.bijective_of_isIso
    (((toPresheaf R₀).map ((sheafificationAdjunction α).unit.app M)).app U)

/-- The sections of a presheaf of modules that is already a sheaf, identified with the sections of
its sheafification. -/
noncomputable def unitAppEquiv (hM : Presheaf.IsSheaf J M.presheaf) (U : Cᵒᵖ) :
    M.obj U ≃ₗ[R₀.obj U]
      ((SheafOfModules.forget R ⋙ restrictScalars α).obj
        ((sheafification α).obj M)).obj U :=
  LinearEquiv.ofBijective (((sheafificationAdjunction α).unit.app M).app U).hom
    (bijective_unit_app_app_of_isSheaf α M hM U)

/-- `unitAppEquiv` sends a section to its image under the sheafification unit. -/
@[simp]
theorem unitAppEquiv_apply (hM : Presheaf.IsSheaf J M.presheaf) (U : Cᵒᵖ) (x : M.obj U) :
    unitAppEquiv α M hM U x = Hom.app ((sheafificationAdjunction α).unit.app M) U x :=
  rfl

end PresheafOfModules

end
