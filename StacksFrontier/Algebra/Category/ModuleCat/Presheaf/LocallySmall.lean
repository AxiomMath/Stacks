module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Presheaves of modules on an essentially small category are locally small

Let `C` be a category which is essentially small relative to a universe `w`, and let `R` be a
presheaf of rings on `C`. The morphisms of `PresheafOfModules.{w} R` are families of maps indexed
by the objects of `C`, so they live in a universe containing that of the objects of `C`; but a
morphism is determined by its components on a small model of `C`, so the category is locally
small relative to `w`.

## Main results

* `PresheafOfModules.locallySmall_of_essentiallySmall` — `LocallySmall.{w}
  (PresheafOfModules.{w} R)` for `R` a presheaf of rings on an essentially `w`-small category.

## Implementation notes

The forgetful functor to presheaves of abelian groups is faithful, and the presheaves of abelian
groups on `C` are equivalent to those on a small model of `C`, which are locally small by the
Mathlib instance for functor categories out of a small category. The result is a theorem and not
an instance because essential smallness is typically a theorem as well.
-/

@[expose] public section

open CategoryTheory

universe w v₁ u₁ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- Presheaves of modules, with values in `w`, on an essentially `w`-small category are locally
`w`-small. -/
public theorem locallySmall_of_essentiallySmall [EssentiallySmall.{w} C] :
    LocallySmall.{w} (PresheafOfModules.{w} R) :=
  have : LocallySmall.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
    (locallySmall_congr ((equivSmallModel.{w} Cᵒᵖ).congrLeft (E := AddCommGrpCat.{w}))).2
      inferInstance
  locallySmall_of_faithful (toPresheaf.{w} R)

end PresheafOfModules

end
