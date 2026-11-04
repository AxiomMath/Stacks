module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPrecomposeExact
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyTildeDerived
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.CanonicalSectionsWithSupportTriangle
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalToGlobalSectionsWithSupport

/-!
# Local cohomology is the derived functor of sections with support, on `Spec A`

Let `A` be a commutative ring, let `I ⊆ A` be a finitely generated ideal, let `X = Spec A` and
`Z = V(I)`. This module proves [Stacks, Tag 0A6T] with both sides as the source defines them:
for `K ∈ D(A)` with associated complex `K̃ ∈ D_QCoh(𝒪_X)` ([Stacks, Tag 06Z0]) there is an
isomorphism

`RΓ_Z(K) ≅ RΓ_Z(X, K̃)`

in `D(A)`, natural in `K`, where on the left is the local cohomology functor of
[Stacks, Tag 0A6Q] and on the right is the total right derived functor
`RΓ_Z(X, -) : D(𝒪_X) ⥤ D(𝒪_X(X))` of sections with support in `Z` of [Stacks, Section 0G6Y]
(`Stacks.Cohomology.SectionsWithSupport.canonicalDerivedSectionsWithSupport`), read in `D(A)` by
restriction of scalars along the canonical isomorphism `A ≅ 𝒪_X(X)`.

## Main results

* `Stacks.LocalCohomologyTilde.derivedSupportedPushforwardGlobalSectionsIso`: for a closed subset
  `Z` of any ringed space `X`, `RΓ(X, i_* R𝓗_Z(-)) ≅ RΓ_Z(X, -)` as functors
  `D(𝒪_X) ⥤ D(𝒪_X(X))`.
* `Stacks.LocalCohomologyTilde.derivedGlobalSectionsToBaseIso`: on `X = Spec A`, the derived
  global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(𝒪_X(X))` read over `A` is the `A`-linear derived global
  sections functor of Tag 06Z0.
* `Stacks.LocalCohomologyTilde.localCohomologyIsoDerivedSectionsWithSupport`: **Tag 0A6T**.

## References

* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0G70](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SectionsWithSupport
open Stacks.Cohomology.LocalToGlobalSupport
open Stacks.Perfect.SupportedQuasicoherent
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections

-- Standard model only: `canonicalDerivedSectionsWithSupport`, `derivedSectionsWithSupportIso`.
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomologyTilde

/-! ### `RΓ(X, i_* R𝓗_Z(-)) = RΓ_Z(X, -)` on a ringed space -/

section RingedSpace

variable (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)

/-- `i_* ⋙ RΓ(X, -)`, with the unit induced by that of `RΓ(X, -)`, is a right derived functor of
`Γ(Z, -) = Γ(X, i_*(-))`. -/
theorem isRightDerivedFunctor_pushforward_comp_canonicalDerivedGlobalSections :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
        canonicalDerivedGlobalSections X).IsRightDerivedFunctor
      (Stacks.DerivedFunctor.precomposeUnit (modulePushforward (closedSubsetInclusion X Z))
        (_root_.SheafOfModules.evaluation (structureSheafRing X) (op ⊤))
        (canonicalDerivedGlobalSections X) (canonicalDerivedGlobalSectionsUnit X) :
        (closedSubspaceGlobalSections X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ _)
      (HomotopyCategory.quasiIso (ClosedModuleSheaves X Z) (ComplexShape.up ℤ)) :=
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := preservesFiniteLimits_modulePullback_closedSubsetInclusion X Z
  let := (modulePullbackPushforwardAdjunction
    (closedSubsetInclusion X Z)).leftAdjoint_preservesColimits
  Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint _ _ _ _
    (modulePullback (closedSubsetInclusion X Z))
    (modulePullbackPushforwardAdjunction (closedSubsetInclusion X Z))
    (Stacks.Cohomology.sheaf_exists_kInjective_resolution X)
    (Stacks.Cohomology.sheaf_exists_kInjective_resolution (closedSubsetRingedSpace X Z))

/-- **`RΓ(X, i_* R𝓗_Z(-)) ≅ RΓ_Z(X, -)`** as functors `D(𝒪_X) ⥤ D(𝒪_X(X))`, for a closed subset
`Z` of a ringed space `X`: [Stacks, Tag 0G70] at the right derived functor `i_* ⋙ RΓ(X, -)` of
`Γ(Z, -)`. -/
def derivedSupportedPushforwardGlobalSectionsIso :
    derivedSupportedPushforward X Z hZ ⋙ canonicalDerivedGlobalSections X ≅
      canonicalDerivedSectionsWithSupport X Z hZ :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  Functor.associator _ _ _ ≪≫
    @derivedSectionsWithSupportIso X Z hZ
      ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
        canonicalDerivedGlobalSections X)
      (Stacks.DerivedFunctor.precomposeUnit (modulePushforward (closedSubsetInclusion X Z))
        (_root_.SheafOfModules.evaluation (structureSheafRing X) (op ⊤))
        (canonicalDerivedGlobalSections X) (canonicalDerivedGlobalSectionsUnit X))
      (canonicalDerivedSectionsWithSupport X Z hZ) (canonicalDerivedSectionsWithSupportUnit X Z hZ)
      (isRightDerivedFunctor_pushforward_comp_canonicalDerivedGlobalSections X Z hZ)
      inferInstance

end RingedSpace

/-! ### Reading `RΓ(Spec A, -)` over `A` -/

section Spec

variable (A : CommRingCat.{u})

/-- `A`-linear global sections on `Spec A`, at the spelling of modules over the structure sheaf of
the underlying ringed space: global sections followed by restriction of scalars along
`A ≅ 𝒪_X(X)`. -/
abbrev globalSectionsToBase :
    ModuleSheaves (Spec A).toRingedSpace ⥤ ModuleCat.{u} A :=
  _root_.SheafOfModules.evaluation (structureSheafRing (Spec A).toRingedSpace) (op ⊤) ⋙
    globalToBase A

/-- The comparison of the degreewise functors underlying `RΓ(X, -)` followed by restriction of
scalars and `A`-linear global sections. -/
def homotopyGlobalSectionsToBaseIso :
    homotopyToDerived (Spec A).toRingedSpace
        (_root_.SheafOfModules.evaluation (structureSheafRing (Spec A).toRingedSpace) (op ⊤)) ⋙
      (globalToBase A).mapDerivedCategory ≅
      (globalSectionsToBase A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (globalToBase A).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (globalSectionsToBase A))
        (ComplexShape.up ℤ))
      DerivedCategory.Qh

/-- On a `K`-injective complex, the unit of `RΓ(X, -)` followed by restriction of scalars is an
isomorphism. -/
private theorem isIso_whiskerRight_unit_app_quotient
    {I : CochainComplex (SheafOfModules (structureSheafRing (Spec A).toRingedSpace)) ℤ}
    (hI : I.IsKInjective) :
    IsIso ((Functor.whiskerRight (canonicalDerivedGlobalSectionsUnit (Spec A).toRingedSpace)
      (globalToBase A).mapDerivedCategory).app ((HomotopyCategory.quotient _ _).obj I)) :=
  have : IsIso ((canonicalDerivedGlobalSectionsUnit (Spec A).toRingedSpace).app
      ((HomotopyCategory.quotient _ _).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective _
      (Stacks.Cohomology.sheaf_exists_kInjective_resolution (Spec A).toRingedSpace)).2
      DerivedCategory.Qh (canonicalDerivedGlobalSections _) (canonicalDerivedGlobalSectionsUnit _)
      I hI
  inferInstanceAs (IsIso ((globalToBase A).mapDerivedCategory.map
    ((canonicalDerivedGlobalSectionsUnit (Spec A).toRingedSpace).app
      ((HomotopyCategory.quotient _ _).obj I))))

/-- `RΓ(X, -)` followed by restriction of scalars is a right derived functor of the global
sections functor followed by restriction of scalars. -/
theorem isRightDerivedFunctor_canonicalDerivedGlobalSections_comp_globalToBase :
    (canonicalDerivedGlobalSections (Spec A).toRingedSpace ⋙
        (globalToBase A).mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight (canonicalDerivedGlobalSectionsUnit (Spec A).toRingedSpace)
        (globalToBase A).mapDerivedCategory)
      (HomotopyCategory.quasiIso (ModuleSheaves (Spec A).toRingedSpace) (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.isRightDerivedFunctor_of_isIso_on_kInjectives
    (Stacks.Cohomology.sheaf_exists_kInjective_resolution (Spec A).toRingedSpace) _ _ _
    (fun _ hI => isIso_whiskerRight_unit_app_quotient A hI)

/-- The unit of `RΓ(X, -)` followed by restriction of scalars, read as a comparison out of
`A`-linear global sections at the spelling `(Spec A).Modules` of the source category. -/
def canonicalDerivedGlobalSectionsToBaseUnit :
    homotopyGlobalSectionsOver (𝟙 (Spec A)) ⟶
      (DerivedCategory.Qh : HomotopyCategory (Spec A).Modules (ComplexShape.up ℤ) ⥤ _) ⋙
        (canonicalDerivedGlobalSections (Spec A).toRingedSpace ⋙
          (globalToBase A).mapDerivedCategory :
          DerivedCategory (Spec A).Modules ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  (homotopyGlobalSectionsToBaseIso A).inv ≫
    Functor.whiskerRight (canonicalDerivedGlobalSectionsUnit (Spec A).toRingedSpace)
      (globalToBase A).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- `RΓ(X, -)` followed by restriction of scalars is a right derived functor of `A`-linear global
sections, at the spelling `(Spec A).Modules` of the source category. -/
theorem isRightDerivedFunctor_canonicalDerivedGlobalSectionsToBase :
    (canonicalDerivedGlobalSections (Spec A).toRingedSpace ⋙
        (globalToBase A).mapDerivedCategory :
        DerivedCategory (Spec A).Modules ⥤ DerivedCategory (ModuleCat.{u} A)).IsRightDerivedFunctor
      (canonicalDerivedGlobalSectionsToBaseUnit A)
      (HomotopyCategory.quasiIso (Spec A).Modules (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.isRightDerivedFunctor_of_isIso_on_kInjectives
    (Scheme.Modules.exists_quasiIso_isKInjective (Spec A)) _ _ _ (fun I hI => ?_)
  have hI' := isIso_whiskerRight_unit_app_quotient A hI
  exact IsIso.comp_isIso'
    (inferInstanceAs (IsIso ((homotopyGlobalSectionsToBaseIso A).inv.app
      ((HomotopyCategory.quotient _ _).obj I))))
    (IsIso.comp_isIso' hI' (inferInstanceAs (IsIso (𝟙 _))))

/-- **`RΓ(Spec A, -)` read over `A` is the `A`-linear derived global sections functor.** -/
def derivedGlobalSectionsToBaseIso :
    (canonicalDerivedGlobalSections (Spec A).toRingedSpace ⋙
        (globalToBase A).mapDerivedCategory :
        DerivedCategory (Spec A).Modules ⥤ DerivedCategory (ModuleCat.{u} A)) ≅
      derivedGlobalSectionsOver (𝟙 (Spec A)) :=
  haveI := isRightDerivedFunctor_canonicalDerivedGlobalSectionsToBase A
  Functor.rightDerivedUnique _ _ (canonicalDerivedGlobalSectionsToBaseUnit A)
    (derivedGlobalSectionsOverUnit (𝟙 (Spec A)))
    (HomotopyCategory.quasiIso (Spec A).Modules (ComplexShape.up ℤ))

end Spec

/-! ### Tag 0A6T -/

section Main

variable {A : CommRingCat.{u}} {I : Ideal A} (hI : I.FG)

/-- `RΓ(X, i_* R𝓗_Z(K̃))`, the functor `derivedSupportedTilde`, written without the
corestrictions to `D_QCoh` and `D_{QCoh, Z}`. -/
def derivedSupportedTildeIso :
    derivedSupportedTilde hI ≅
      (tildeSheafFunctor A).mapDerivedCategory ⋙
        derivedSupportedPushforward (Spec A).toRingedSpace (vanishingSet A I)
          (isClosed_vanishingSet A I) ⋙
        derivedGlobalSectionsOver (𝟙 (Spec A)) :=
  (Functor.associator (derivedTilde A) (derivedQCoh A).ι
      (derivedSupportedPushforward (Spec A).toRingedSpace (vanishingSet A I)
          (isClosed_vanishingSet A I) ⋙
        derivedGlobalSectionsOver (𝟙 (Spec A)))).symm ≪≫
    Functor.isoWhiskerRight (derivedTildeCompι A)
      (derivedSupportedPushforward (Spec A).toRingedSpace (vanishingSet A I)
          (isClosed_vanishingSet A I) ⋙
        derivedGlobalSectionsOver (𝟙 (Spec A)))

/-- Let `A` be a ring, let `I ⊆ A` be a finitely generated ideal and set `Z = V(I) ⊆ X = Spec A`.
For `K ∈ D(A)`, corresponding to `K̃ ∈ D_QCoh(𝒪_X)` by [Stacks, Tag 06Z0], there is an
isomorphism

`RΓ_Z(K) ≅ RΓ_Z(X, K̃)`

in `D(A)`, functorial in `K`. On the left is the local cohomology functor of
[Stacks, Tag 0A6Q], followed by the inclusion of the complexes with `I`-power-torsion cohomology
into `D(A)`. On the right is the total right derived functor
`RΓ_Z(X, -) : D(𝒪_X) ⥤ D(𝒪_X(X))` of `F ↦ Γ_Z(X, F)` on the unbounded derived category, as in
[Stacks, Section 0G6Y], applied to `K̃` and read as a complex of `A`-modules by restriction of
scalars along the canonical isomorphism `A ≅ 𝒪_X(X)`.

The ring is arbitrary, `K` is an arbitrary object of the unbounded derived category, and the
only hypothesis on `I` is finite generation. -/
@[stacks 0A6T]
def localCohomologyIsoDerivedSectionsWithSupport :
    Dualizing.localCohomologyFunctor (A : Type u) I hI ⋙
        (Dualizing.derivedPowerTorsionProperty (A : Type u) I hI).ι ≅
      (tildeSheafFunctor A).mapDerivedCategory ⋙
        canonicalDerivedSectionsWithSupport (Spec A).toRingedSpace (vanishingSet A I)
          (isClosed_vanishingSet A I) ⋙
        (globalToBase A).mapDerivedCategory :=
  localCohomologyDerivedSupportedTildeIso hI ≪≫ derivedSupportedTildeIso hI ≪≫
    Functor.isoWhiskerLeft (tildeSheafFunctor A).mapDerivedCategory
      (Functor.isoWhiskerLeft _ (derivedGlobalSectionsToBaseIso A).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (derivedSupportedPushforwardGlobalSectionsIso (Spec A).toRingedSpace (vanishingSet A I)
            (isClosed_vanishingSet A I))
          (globalToBase A).mapDerivedCategory)

end Main

end Stacks.LocalCohomologyTilde

end
