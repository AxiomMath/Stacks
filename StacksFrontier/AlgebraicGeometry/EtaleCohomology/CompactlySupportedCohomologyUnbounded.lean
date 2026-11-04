module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology with compact support on the unbounded derived category

Let `f : X ⟶ Spec k` be a separated finite type morphism and let `Λ` be a ring. Choosing a
compactification `j : X ⟶ Xbar` of `X` over `Spec k`, the derived lower shriek functor
`Rf_! = R(fbar)_* ∘ Rj_!` and the cohomology with compact support
`RΓ_c(X, K) = RΓ(Spec k, Rf_! K)` are defined on the whole unbounded derived category
`D(X_étale, Λ)`, as in [Stacks, Tag 0GJZ].

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded`,
  `etaleModuleDerivedExtensionByZeroUnbounded` and
  `etaleModuleDerivedGlobalSectionsUnbounded`: the total right derived functors of `f_*`, `j_!`
  and `Γ` on unbounded derived categories of sheaves of `Λ`-modules on small étale sites.
* `Stacks.EtaleCohomology.derivedLowerShriekUnbounded`: the functor `Rf_!` on `D(X_étale, Λ)`.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyUnbounded`: the complex `RΓ_c(X, K)` for
  `K` in `D(X_étale, Λ)`.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyGroupUnbounded`: the module `H^i_c(X, K)`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedDirectImageUnboundedUnit_app` and its
  analogues for `j_!` and `Γ`: each of the three derived functors is computed on a K-injective
  resolution.

## Implementation notes

Sheaves of `Λ`-modules on a small étale site form a Grothendieck abelian category, so every
cochain complex has a functorial K-injective resolution and Spaltenstein's theorem
`Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q`
produces the total right derived functor of any additive functor out of it on the whole of
`D(X_étale, Λ)`, with no boundedness or hypothesis on `Λ`.

Each derived functor comes with its derivation unit at the level of cochain complexes and with
the universal property, `CategoryTheory.Functor.IsRightDerivedFunctor`, which characterises it
up to a unique natural isomorphism.

The source states the unbounded case for a torsion ring `Λ`; the formula uses no such
hypothesis, so the definitions below are given for an arbitrary ring. The compactification is an
explicit argument.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution (hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
  invertsQuasiIso_mapHomologicalComplex_comp_Q isIso_app_of_isKInjective)

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

section Derived

variable (Λ : Type r) [Ring Λ]

/-- The unbounded derived direct image `Rf_*` of sheaves of `Λ`-modules on small étale sites:
the total right derived functor of `f_*` along the localization of cochain complexes. -/
def etaleModuleDerivedDirectImageUnbounded {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤ DerivedCategory (EtaleModules.{u, r} Λ Y) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (etaleModuleDirectImage.{u, r} Λ f)
  ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

/-- The derivation unit of `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded`:
the comparison from the degreewise direct image of a complex to its derived direct image. -/
def etaleModuleDerivedDirectImageUnboundedUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (etaleModuleDirectImage.{u, r} Λ f)
  ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

/-- `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded` is a total right derived
functor of `f_*`, the universal property characterising it. -/
instance etaleModuleDerivedDirectImageUnbounded_isRightDerivedFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).IsRightDerivedFunctor
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (etaleModuleDirectImage.{u, r} Λ f)
  inferInstanceAs ((((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X)
        (ComplexShape.up ℤ))).IsRightDerivedFunctor
    (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)))
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)))

/-- The unbounded derived extension by zero `Rj_!` of sheaves of `Λ`-modules along an étale
morphism: the total right derived functor of `j_!`. -/
def etaleModuleDerivedExtensionByZeroUnbounded {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    DerivedCategory (EtaleModules.{u, r} Λ U) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (etaleModuleExtensionByZero.{u, r} Λ j)
  ((etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ U) (ComplexShape.up ℤ))

/-- The derivation unit of
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnbounded`. -/
def etaleModuleDerivedExtensionByZeroUnboundedUnit {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (etaleModuleExtensionByZero.{u, r} Λ j)
  ((etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ U) (ComplexShape.up ℤ))

/-- `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnbounded` is a total right derived
functor of `j_!`, the universal property characterising it. -/
instance etaleModuleDerivedExtensionByZeroUnbounded_isRightDerivedFunctor
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).IsRightDerivedFunctor
      (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ U) (ComplexShape.up ℤ)) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (etaleModuleExtensionByZero.{u, r} Λ j)
  inferInstanceAs ((((etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ U)
        (ComplexShape.up ℤ))).IsRightDerivedFunctor
    (((etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ U) (ComplexShape.up ℤ)))
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ U) (ComplexShape.up ℤ)))

/-- The unbounded derived global sections `RΓ(X, -)` of sheaves of `Λ`-modules on the small
étale site of `X`: the total right derived functor of `Γ`. -/
def etaleModuleDerivedGlobalSectionsUnbounded (X : Scheme.{u}) :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤ DerivedCategory (ModuleCat.{max (u + 1) r} Λ) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (etaleModuleGlobalSections.{u, r} Λ X)
  ((etaleModuleGlobalSections.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

/-- The derivation unit of
`Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnbounded`. -/
def etaleModuleDerivedGlobalSectionsUnboundedUnit (X : Scheme.{u}) :
    (etaleModuleGlobalSections.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ X :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (etaleModuleGlobalSections.{u, r} Λ X)
  ((etaleModuleGlobalSections.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

/-- `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnbounded` is a total right derived
functor of `Γ`, the universal property characterising it. -/
instance etaleModuleDerivedGlobalSectionsUnbounded_isRightDerivedFunctor (X : Scheme.{u}) :
    (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ X).IsRightDerivedFunctor
      (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ X)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (etaleModuleGlobalSections.{u, r} Λ X)
  inferInstanceAs ((((etaleModuleGlobalSections.{u, r} Λ X).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X)
        (ComplexShape.up ℤ))).IsRightDerivedFunctor
    (((etaleModuleGlobalSections.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)))
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)))

/-! ### The three derived functors are computed on K-injective complexes -/

/-- On a K-injective complex the unit of the derivation of `f_*` is invertible, so `Rf_*` is
computed by the degreewise direct image of a K-injective resolution. -/
theorem isIso_etaleModuleDerivedDirectImageUnboundedUnit_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hK : K.IsKInjective) :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) :=
  isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (etaleModuleDirectImage.{u, r} Λ f)) K hK

/-- On a K-injective complex the unit of the derivation of `j_!` is invertible, so `Rj_!` is
computed by the degreewise extension by zero of a K-injective resolution. -/
theorem isIso_etaleModuleDerivedExtensionByZeroUnboundedUnit_app {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (K : CochainComplex (EtaleModules.{u, r} Λ U) ℤ) (hK : K.IsKInjective) :
    IsIso ((etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j).app K) :=
  isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (etaleModuleExtensionByZero.{u, r} Λ j)) K hK

/-- On a K-injective complex the unit of the derivation of `Γ` is invertible, so `RΓ(X, -)` is
computed by the degreewise global sections of a K-injective resolution. -/
theorem isIso_etaleModuleDerivedGlobalSectionsUnboundedUnit_app (X : Scheme.{u})
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hK : K.IsKInjective) :
    IsIso ((etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ X).app K) :=
  isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (etaleModuleGlobalSections.{u, r} Λ X)) K hK

end Derived

/-! ### Cohomology with compact support on `D(X_étale, Λ)` -/

/-- The derived lower shriek functor `Rf_! = R(fbar)_* ∘ Rj_!` attached to a compactification
`j : X ⟶ Xbar` of `X` over `Y`, on the unbounded derived categories of sheaves of `Λ`-modules for
the small étale topologies ([Stacks, Tag 0F7H]). -/
abbrev derivedLowerShriekUnbounded {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤ DerivedCategory (EtaleModules.{u, r} Λ Y) :=
  etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]

/-- The cohomology with compact support `RΓ_c(X, K) = RΓ(Spec k, Rf_! K)` of an arbitrary
complex of sheaves of `Λ`-modules on the small étale site of a separated finite type `k`-scheme
`X`, through a compactification `j`. -/
@[stacks 0GJZ "RΓ_c(X, K) = RΓ(Spec k, Rf_! K) on D(X_étale, Λ)",
  sga "4½ Rapport 3.6",
  sga "7 XXII 3.4" "more general"]
abbrev compactlySupportedCohomologyUnbounded (j : CompactificationOf (Over.mk f))
    (Λ : Type r) [Ring Λ] :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤ DerivedCategory (ModuleCat.{max (u + 1) r} Λ) :=
  derivedLowerShriekUnbounded.{u, r} f j Λ ⋙
    etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of k))

/-- The compactly supported cohomology module `H^i_c(X, K) = H^i(RΓ_c(X, K))` of an arbitrary
complex `K` in `D(X_étale, Λ)`. -/
@[stacks 0GJZ "H^i_c(X, K) = H^i(RΓ_c(X, K)) on D(X_étale, Λ)"]
abbrev compactlySupportedCohomologyGroupUnbounded (j : CompactificationOf (Over.mk f))
    (Λ : Type r) [Ring Λ] (i : ℤ) :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤ ModuleCat.{max (u + 1) r} Λ :=
  compactlySupportedCohomologyUnbounded.{u, r} k f j Λ ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i

end Stacks.EtaleCohomology

end
