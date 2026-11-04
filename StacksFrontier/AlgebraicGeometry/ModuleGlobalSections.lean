module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Global sections of sheaves of modules on a scheme

`Γ(X, -)` as an additive functor from sheaves of `𝒪_X`-modules to modules over the ring
`Γ(X, 𝒪_X)` of global functions, and more generally the sections over an open `U` as an additive
functor to modules over `Γ(X, U)`.

## Main definitions

* `AlgebraicGeometry.sectionsOn`: sections over an open `U`, as a functor
  `X.Modules ⥤ ModuleCat Γ(X, U)`.
* `AlgebraicGeometry.moduleGlobalSections`: the global-sections functor
  `X.Modules ⥤ ModuleCat Γ(X, ⊤)`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- **Sections over an open.** Sections over `U ⊆ X` of a sheaf of `𝒪_X`-modules, as a module
over the ring `Γ(U, 𝒪_X)` of functions on `U`. -/
abbrev sectionsOn (X : Scheme.{u}) (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

/-- Sections over an open form an additive functor; addition of sections of a sheaf of modules
is computed open by open. -/
instance sectionsOn_additive (X : Scheme.{u}) (U : X.Opens) : (sectionsOn X U).Additive where
  map_add := rfl

/-- The sections functor sends a module to its module of sections over `U`. -/
@[simp] theorem sectionsOn_obj {X : Scheme.{u}} (U : X.Opens) (F : X.Modules) :
    (sectionsOn X U).obj F = ModuleCat.of Γ(X, U) Γ(F, U) := rfl

/-- The sections functor sends a morphism of modules to its action on sections over `U`. -/
@[simp] theorem sectionsOn_map_apply {X : Scheme.{u}} (U : X.Opens) {F G : X.Modules} (φ : F ⟶ G)
    (x : Γ(F, U)) : ((sectionsOn X U).map φ).hom x = φ.app U x := rfl

/-- **Global sections of sheaves of modules on a scheme.** `Γ(X, -)` as an additive functor from
sheaves of `𝒪_X`-modules to modules over the ring `Γ(X, 𝒪_X)` of global functions. -/
abbrev moduleGlobalSections (X : Scheme.{u}) : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤)

/-- Global sections of sheaves of modules is additive; addition of sections of a sheaf of
modules is computed open by open. -/
instance moduleGlobalSections_additive (X : Scheme.{u}) :
    (moduleGlobalSections X).Additive where

/-- Global sections of sheaves of modules preserves finite limits; it is an evaluation, and
evaluation of sheaves of modules is computed open by open. -/
instance moduleGlobalSections_preservesFiniteLimits (X : Scheme.{u}) :
    CategoryTheory.Limits.PreservesFiniteLimits (moduleGlobalSections X) := by
  change CategoryTheory.Limits.PreservesFiniteLimits
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
  infer_instance

end AlgebraicGeometry

end
