module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact

/-!
# Local injectivity suffices for a monomorphism of sheaves of modules

A morphism of sheaves of modules on a site is a monomorphism as soon as its underlying
morphism of presheaves of abelian groups is *locally* injective: two sections with the same
image agree on a covering sieve, and the source being a sheaf they are therefore equal.

## Main results

* `Stacks.SheafOfModules.injective_app_of_isLocallyInjective`
* `Stacks.SheafOfModules.mono_of_isLocallyInjective`

## Implementation notes

The content is `CategoryTheory.Presheaf.isLocallyInjective_iff_injective_of_separated`, which
is stated for presheaves valued in a concrete category; a sheaf of modules is not of that form,
but its underlying presheaf of abelian groups is, and
`CategoryTheory.PresheafOfModules.toPresheaf` composed with
`CategoryTheory.SheafOfModules.forget` is a faithful functor to it, so monomorphisms are
reflected.  Nothing here needs the site to come from a topological space.
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.SheafOfModules

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

variable {M N : _root_.SheafOfModules.{w} R} (φ : M ⟶ N)

/-- A locally injective morphism of sheaves of modules is injective on the sections over
every object of the site. -/
theorem injective_app_of_isLocallyInjective
    (hφ : CategoryTheory.Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map φ.val)) (U : Cᵒᵖ) :
    Function.Injective (((PresheafOfModules.toPresheaf R.obj).map φ.val).app U) :=
  (CategoryTheory.Presheaf.isLocallyInjective_iff_injective_of_separated J
    ((PresheafOfModules.toPresheaf R.obj).map φ.val) (isSeparated_presheaf M)).mp hφ U

/-- A locally injective morphism of sheaves of modules is a monomorphism. -/
theorem mono_of_isLocallyInjective
    (hφ : CategoryTheory.Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map φ.val)) :
    Mono φ :=
  Functor.mono_of_mono_map
    (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)
    ((NatTrans.mono_iff_mono_app _).mpr fun U =>
      ConcreteCategory.mono_of_injective _ (injective_app_of_isLocallyInjective φ hφ U))

end Stacks.SheafOfModules
