module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Modules under the localization of a ringed site

Let `(C, O)` be a ringed site and `U` an object of `C`. The localization morphism of ringed
topoi `π : (Sh(C/U), O|_U) ⟶ (Sh(C), O)` of Stacks 04IX carries sheaves of modules in both
directions, and this file records the direct image `j_{U*}` it induces.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationDirectImage`: the direct image of sheaves of
  modules along the localization morphism at `U`.

## Main results

* `AlgebraicGeometry.RingedSite.moduleRestriction_obj`: the sections of a restricted sheaf of
  modules over an object `V ⟶ U` of the localized site are the sections of the original sheaf
  over `V`.

## Implementation notes

The direct image is the module pushforward of the localization morphism, so it is introduced as
an abbreviation rather than a new definition: the functorial and underlying-sheaf API of
`Stacks.Sheaves.RingedToposModules.pushforwardModules` applies to it unchanged, which is the
point of stating it this way.

Restriction of sheaves of modules to the localized site is Mathlib's `SheafOfModules.over`
and `SheafOfModules.overFunctor`, so it is not redefined here; what is recorded is its effect
on sections, which holds by `rfl` because the restricted presheaf is reindexing along
`Over.forget U`.

The source and target of the direct image are spelled with
`AlgebraicGeometry.RingedSite.ringSheaf` rather than with
`Stacks.SheafOfModules.Tensor.ringSheaf` of the associated ringed topos; the two agree by
`AlgebraicGeometry.RingedSite.ringSheaf_ringedTopos`, which holds by `rfl`.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

-- Restriction of a sheaf of modules to the localized site is Mathlib's `SheafOfModules.over`,
-- and its functoriality is `SheafOfModules.overFunctor`; these are the objects Stacks 04IX (4)
-- names, so the tag is registered on them rather than on a redefinition.
add_to_stacks 04IX "module_restriction" SheafOfModules.over
add_to_sga "3 I 3.1.4" "more general" SheafOfModules.over
add_to_sga "4 IV 11.2.2" SheafOfModules.over
add_to_sga "4 Vbis 1.3.7" "special case" SheafOfModules.over
add_to_stacks 04IX "module_restriction" SheafOfModules.overFunctor
add_to_sga "3 I 3.1.4" "more general" SheafOfModules.overFunctor
add_to_sga "4 IV 11.2.2" SheafOfModules.overFunctor
add_to_sga "4 Vbis 1.3.7" "special case" SheafOfModules.overFunctor

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v w}) (U : X.C)

/-- Direct image of sheaves of modules under the localization morphism at `U`. -/
@[sga "4 IV 13.2.1" "localization morphism"]
noncomputable abbrev localizationDirectImage :
    SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ⥤
      SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  pushforwardModules (X := ringedTopos (X.over U)) (Y := ringedTopos X)
    (X.localizationMorphism U)

/-- The sections of a restricted sheaf of modules over an object `V ⟶ U` of the localized site
are the sections of the original sheaf over `V`: restriction is reindexing along
`Over.forget U`. -/
@[simp, stacks 04IX "module_restriction"]
theorem moduleRestriction_obj {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (F : SheafOfModules.{w} R) (U : C) (V : (Over U)ᵒᵖ) :
    ((F.over U).val.presheaf.obj V : Type w) =
      (F.val.presheaf.obj (Opposite.op V.unop.left) : Type w) :=
  rfl

end AlgebraicGeometry.RingedSite
