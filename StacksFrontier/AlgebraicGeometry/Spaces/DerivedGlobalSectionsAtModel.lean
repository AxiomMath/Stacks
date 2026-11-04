module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedCoheratorGlobalSections

/-!
# Derived global sections on the small étale site at any model of the derived category

`RΓ(X, -) : D(𝒪_X) ⥤ D(Γ(X, 𝒪_X))` for an algebraic space `X`, the total right derived functor
of global sections of `𝒪_X`-modules on the whole unbounded derived category, at any model of
`D(𝒪_X)`.  It exists with no hypothesis: the `𝒪_X`-modules are Grothendieck abelian at `u`, so
every cochain complex of them has a K-injective resolution.

## Main definitions

* `AlgebraicGeometry.Space.derivedModuleGlobalSectionsSmallEtaleAtModel`: `RΓ(X, -)` at any
  model of `D(𝒪_X)`; `AlgebraicGeometry.Space.derivedModuleGlobalSectionsSmallEtale` is the same
  functor at the model `AlgebraicGeometry.Space.modulesHasDerivedCategorySmallEtale`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `RΓ(X, -) : D(𝒪_X) ⥤ D(Γ(X, 𝒪_X))`, the total right derived functor of global sections of
`𝒪_X`-modules, at any model of `D(𝒪_X)`; `derivedModuleGlobalSectionsSmallEtale` is the same
functor at the model `modulesHasDerivedCategorySmallEtale`. -/
abbrev derivedModuleGlobalSectionsSmallEtaleAtModel (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    [@HasDerivedCategory.{w} (Modules.{u, u} B S hS F hF) _
      (modulesAbelianSmallEtale B S hS F hF)] :
    letI := modulesAbelianSmallEtale B S hS F hF
    letI := isGrothendieckAbelian_modules B S hS F hF
    DerivedCategory (Modules.{u, u} B S hS F hF) ⥤
      DerivedCategory (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS F hF)) :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := isGrothendieckAbelian_modules B S hS F hF
  ((moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))

end AlgebraicGeometry.Space

end
