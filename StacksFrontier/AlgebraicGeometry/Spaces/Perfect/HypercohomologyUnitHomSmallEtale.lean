module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsUnitHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableCohomologyQcqsEtale

/-!
# Hypercohomology of an algebraic space in abelian groups is morphisms out of `𝒪_X`

Let `X` be an algebraic space over a scheme `S` and let `Z` be an object of `D(𝒪_X)`.  This file
identifies the hypercohomology group `H^n(X, Z)` — the degree-`n` cohomology of the **abelian
group valued** unbounded derived global sections
`AlgebraicGeometry.Space.derivedGlobalSectionsAb` — with the group of morphisms
`𝒪_X[0] ⟶ Z⟦n⟧` of `D(𝒪_X)`, naturally in `Z`:

`H^n(RΓ(X, Z)) ≅ Hom_{D(𝒪_X)}(𝒪_X[0], Z⟦n⟧)`.

That is Stacks 08JA at source the structure sheaf, in every degree, which is the `K = 𝒪_X[0]`
case of Stacks 0B6E.  It is the rewrite a consumer computing `Ext` out of hypercohomology needs,
and the one `AlgebraicGeometry.Space.derivedGlobalSectionsAb` did not have: the ringed-site
statements `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` and
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsDegreeEquiv` are proved for a
`AlgebraicGeometry.RingedSite.{u, u, u}`, whereas
`AlgebraicGeometry.Space.smallEtaleRingedSite` is a `AlgebraicGeometry.RingedSite.{u + 1, u, u}`,
so neither of them applies to an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.derivedGlobalSectionsAbIsoForget`: `RΓ(X, -)` in abelian groups is
  `RΓ(X, -)` in `Γ(X, 𝒪_X)`-modules, read on derived categories through the forgetful functor.
* `AlgebraicGeometry.Space.derivedGlobalSectionsAbUnitHomNatIso`: **the identification**
  `H^n(RΓ(X, -)) ≅ Hom(𝒪_X[0], (-)⟦n⟧)`, as an isomorphism of functors `D(𝒪_X) ⥤ AddCommGrpCat`.
* `AlgebraicGeometry.Space.derivedGlobalSectionsAbDegreeEquiv`: the same identification at a
  fixed object, as an isomorphism of abelian groups.

## Main results

* `AlgebraicGeometry.Space.derivedGlobalSectionsAbDegreeEquiv_naturality`: the group isomorphism
  is natural in the object of `D(𝒪_X)`.

## The proof, and the universes

There is nothing to prove about the structure sheaf here, because
`AlgebraicGeometry.Space.cohomologyIsoUnitHomShift` already identifies
`H^n(RΓ(X, -)) ≅ Hom(𝒪_X[0], (-)⟦n⟧)` for the **module valued** derived global sections
`AlgebraicGeometry.Space.derivedModuleGlobalSectionsSmallEtaleAtModel`, naturally and in every
degree: both sides are right derived functors of `L ↦ H^0(Γ(X, L))` on the homotopy category, so
they agree by the uniqueness of right derived functors.  What is missing is only that this is the
same functor as `AlgebraicGeometry.Space.derivedGlobalSectionsAb`, and that is the postcomposition
statement `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso` for the
exact functor `forget₂ (ModuleCat (Γ(X, 𝒪_X))) AddCommGrpCat`, together with the commutation of an
exact functor with cohomology,
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`.

Everything is stated at `AddCommGrpCat.{u + 1}`, not at `AddCommGrpCat.{u}`.  That is forced: the
small étale site of an algebraic space over `S : Scheme.{u}` has its objects in `Type (u + 1)`, so
a compatible family of sections of an `𝒪_X`-module is a `Type (u + 1)`, and both
`AlgebraicGeometry.Space.globalSectionsAb` and
`AlgebraicGeometry.Space.derivedGlobalSectionsAb` take their values there.  The identification
below is the one at the universe where derived global sections of an algebraic space actually
live, and no transport to `AddCommGrpCat.{u}` is claimed.

The `AddCommGrpCat.uliftFunctor.{u + 1, u + 1}` carried by
`AlgebraicGeometry.Space.cohomologyIsoUnitHomShift` is a lift *within* `Type (u + 1)` and is
cancelled rather than transported: it is fully faithful, so
`CategoryTheory.Functor.fullyFaithfulCancelRight` removes it from both sides of the
identification.

## Hypotheses

None, beyond `X` being an algebraic space over `S`.  Every statement below is unconditional.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] ModuleCat.hasDerivedCategory
attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### Exactness of the forgetful functor on `Γ(X, 𝒪_X)`-modules

The four instances below are the exactness of
`forget₂ (ModuleCat.{u + 1} (Γ(X, 𝒪_X))) AddCommGrpCat.{u + 1}`.  They are supplied as terms with
their universes written out because the ring `Γ(X, 𝒪_X)` of an algebraic space lives in
`Type (u + 1)` while the Mathlib instances are stated with the module universe of the shape
`max u w` for a ring in `Type u`, and the universe unifier does not solve `max (u + 1) ?w = u + 1`.
-/

/-- Forgetting the `Γ(X, 𝒪_X)`-module structure preserves colimits. -/
local instance preservesColimits_forget₂_globalSectionRingSmallEtale :
    PreservesColimits (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
      AddCommGrpCat.{u + 1}) :=
  ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} _

/-- Forgetting the `Γ(X, 𝒪_X)`-module structure preserves limits. -/
local instance preservesLimits_forget₂_globalSectionRingSmallEtale :
    PreservesLimits (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
      AddCommGrpCat.{u + 1}) :=
  ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{u + 1, u + 1, u + 1, u + 1}

/-- Forgetting the `Γ(X, 𝒪_X)`-module structure is right exact. -/
local instance preservesFiniteColimits_forget₂_globalSectionRingSmallEtale :
    PreservesFiniteColimits
      (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
        AddCommGrpCat.{u + 1}) :=
  PreservesColimits.preservesFiniteColimits _

/-- Forgetting the `Γ(X, 𝒪_X)`-module structure is left exact. -/
local instance preservesFiniteLimits_forget₂_globalSectionRingSmallEtale :
    PreservesFiniteLimits
      (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
        AddCommGrpCat.{u + 1}) :=
  PreservesLimits.preservesFiniteLimits _

/-! ### The two readings of `RΓ(X, -)` -/

/-- **`RΓ(X, -)` in abelian groups is `RΓ(X, -)` in `Γ(X, 𝒪_X)`-modules, forgotten.**  Global
sections of `𝒪_X`-modules read in abelian groups are global sections read in
`Γ(X, 𝒪_X)`-modules followed by the forgetful functor, which is exact; so the unbounded right
derived functor of the former is the unbounded right derived functor of the latter followed by
the functor the forgetful functor induces on derived categories. -/
def derivedGlobalSectionsAbIsoForget :
    derivedGlobalSectionsAb B S hS X ≅
      derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2 ⋙
        (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1}).mapDerivedCategory :=
  (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
    (moduleGlobalSectionsSmallEtale.{u, u} B S hS X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
      AddCommGrpCat.{u + 1})).symm

/-- **`H^n(X, -)` in abelian groups is `H^n(X, -)` in `Γ(X, 𝒪_X)`-modules, forgotten**, naturally
on `D(𝒪_X)`: `AlgebraicGeometry.Space.derivedGlobalSectionsAbIsoForget` followed by the
commutation of an exact functor with the cohomology of the derived category. -/
def homologyDerivedGlobalSectionsAbIsoForget (n : ℤ) :
    derivedGlobalSectionsAb B S hS X ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n ≅
      derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2 ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) n ⋙
        forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight (derivedGlobalSectionsAbIsoForget B S hS X)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2)
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1}) n)

/-! ### Hypercohomology as morphisms out of the structure sheaf -/

/-- **Stacks 08JA at the structure sheaf, in every degree, on the small étale site of an
algebraic space.**  For every integer `n` the degree-`n` cohomology of the abelian-group valued
derived global sections `RΓ(X, -)` is the group `Hom_{D(𝒪_X)}(𝒪_X[0], (-)⟦n⟧)`, naturally on
`D(𝒪_X)`.  This is the case `K = 𝒪_X[0]` of Stacks 0B6E.

The module-valued form of this identification is
`AlgebraicGeometry.Space.cohomologyIsoUnitHomShift`; what is added here is that it is the
abelian-group valued derived global sections — the functor the cohomology of an algebraic space
is computed with — on the left, with the universe lift it carries cancelled against the one on
the right. -/
def derivedGlobalSectionsAbUnitHomNatIso (n : ℤ) :
    derivedGlobalSectionsAb B S hS X ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n ≅
      shiftFunctor (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) n ⋙
        preadditiveCoyoneda.obj (op (structureDerived X)) :=
  homologyDerivedGlobalSectionsAbIsoForget B S hS X n ≪≫
    Functor.fullyFaithfulCancelRight AddCommGrpCat.uliftFunctor.{u + 1, u + 1}
      (cohomologyIsoUnitHomShift X n)

/-- **Stacks 08JA at the structure sheaf, in every degree, at a fixed object.**  The
hypercohomology group `H^n(RΓ(X, Z))`, computed in abelian groups, is the group of morphisms
`𝒪_X[0] ⟶ Z⟦n⟧` of `D(𝒪_X)`.

This is `AlgebraicGeometry.Space.derivedGlobalSectionsAbUnitHomNatIso` read at `Z` as an
isomorphism of abelian groups. -/
def derivedGlobalSectionsAbDegreeEquiv
    (Z : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((derivedGlobalSectionsAb B S hS X).obj Z) : Type (u + 1)) ≃+
      (structureDerived X ⟶ Z⟦n⟧) :=
  ((derivedGlobalSectionsAbUnitHomNatIso B S hS X n).app Z).addCommGroupIsoToAddEquiv

/-- **The identification of hypercohomology with morphisms out of the structure sheaf is natural
in the object of `D(𝒪_X)`.** -/
theorem derivedGlobalSectionsAbDegreeEquiv_naturality (n : ℤ)
    {Z Z' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (φ : Z ⟶ Z')
    (c : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
      ((derivedGlobalSectionsAb B S hS X).obj Z) : Type (u + 1))) :
    derivedGlobalSectionsAbDegreeEquiv B S hS X Z' n
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
          ((derivedGlobalSectionsAb B S hS X).map φ) c) =
      derivedGlobalSectionsAbDegreeEquiv B S hS X Z n c ≫ φ⟦n⟧' := by
  have h := (derivedGlobalSectionsAbUnitHomNatIso B S hS X n).hom.naturality φ
  exact congrArg (fun f => (AddCommGrpCat.Hom.hom f) c) h

end AlgebraicGeometry.Space

end
