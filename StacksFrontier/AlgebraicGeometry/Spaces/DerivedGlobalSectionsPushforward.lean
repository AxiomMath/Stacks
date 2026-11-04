module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsAtModel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayGlobalSectionsOfToposHomDerivedPullback

/-!
# Derived global sections of a derived direct image of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces. The global-sections clause of Stacks 0D6H
gives `RΓ(Y, -) ∘ Rf_* = RΓ(X, -)` as functors `D(𝒪_X) ⟶ D(Γ(Y, 𝒪_Y))`, the right hand side
with scalars restricted along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. Here `D(𝒪_X)` is the standard model, at
which `Rf_*`, `Lf^*` and the derived internal Hom of algebraic spaces live.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionRingSmallEtaleHom`: the ring map
  `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` of `f`.
* `AlgebraicGeometry.Space.derivedModuleGlobalSectionsRestricted`: `RΓ(X, -)` read in
  `D(Γ(Y, 𝒪_Y))`.
* `AlgebraicGeometry.Space.derivedModulePushforwardGlobalSectionsIso`: Stacks 0D6H for `f`.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] ModuleCat.hasDerivedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- The ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` of a morphism of algebraic spaces, induced on global
sections by its morphism of small étale ringed topoi. -/
abbrev globalSectionRingSmallEtaleHom (f : X ⟶ Y) :
    globalSectionRingSmallEtale B S hS Y.1 Y.2 →+* globalSectionRingSmallEtale B S hS X.1 X.2 :=
  globalSectionsRingHom (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom

/-- `RΓ(X, -) : D(𝒪_X) ⥤ D(Γ(Y, 𝒪_Y))`: derived global sections of `𝒪_X`-modules with scalars
restricted along the ring map of `f : X ⟶ Y`. -/
abbrev derivedModuleGlobalSectionsRestricted (f : X ⟶ Y) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) :=
  letI := isGrothendieckAbelian_modules B S hS X.1 X.2
  Stacks.DerivedFunctor.totalRightDerived
    (moduleGlobalSectionsSmallEtale.{u, u} B S hS X.1 X.2 ⋙
      ModuleCat.restrictScalars (globalSectionRingSmallEtaleHom B S hS f))

/-- **Stacks 0D6H for a morphism of algebraic spaces**, the global-sections clause: for
`f : X ⟶ Y`, `RΓ(Y, -) ∘ Rf_* = RΓ(X, -)` as functors `D(𝒪_X) ⟶ D(Γ(Y, 𝒪_Y))`. -/
def derivedModulePushforwardGlobalSectionsIso (f : X ⟶ Y) :
    derivedModulePushforward B S hS f ⋙
        derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2 ≅
      derivedModuleGlobalSectionsRestricted B S hS f :=
  letI := isGrothendieckAbelian_modules B S hS X.1 X.2
  letI := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (RingCat.sectionsSubring
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (smallEtaleRingedTopos B S hS Y).J)
      (smallEtaleRingedTopos B S hS Y).O)).obj)) :=
    ModuleCat.hasDerivedCategory
  Stacks.Cohomology.LerayUnbounded.derivedGlobalSectionsPushforwardIsoOfToposHom
    (smallEtaleRingedToposHom B S hS f)

end AlgebraicGeometry.Space

end
