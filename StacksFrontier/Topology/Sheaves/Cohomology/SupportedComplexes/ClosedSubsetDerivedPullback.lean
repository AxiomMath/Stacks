module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologyExcisionRingedSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quasi-inverse of Tag 0AEF part (2) is inverse image

Let `Z` be a closed subset of a ringed space `X` and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the
inclusion.  Part (2) of Stacks 0AEF asserts that `i_*^D : D(𝒪_X|_Z) ⥤ D_Z(𝒪_X)` is an
equivalence whose quasi-inverse is *both* `RH_Z` and `i^{-1}`, each restricted to `D_Z(𝒪_X)`.
`Stacks.Cohomology.SupportedComplexes.closedSubsetDerivedPushforwardEquivalence_inverse` records
the first description.  This file proves the second: on `D_Z(𝒪_X)` the functor `RH_Z` agrees with
`i^{-1}`.

Both `i_*` and `i^{-1} = i^*` are exact — the first by Stacks 08KS, the second because the
structure sheaf of `closedSubsetRingedSpace X Z` *is* `i^{-1}𝒪_X`, so no base change takes place
(`Stacks.Cohomology.SupportedComplexes.pullbackExact`) — so each induces a functor on unbounded
derived categories directly, with no resolutions.

## Main results

* `Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedCompIsoId`: a quasi-inverse pair of
  exact functors induces a quasi-inverse pair on unbounded derived categories.
* `Stacks.Cohomology.SupportedComplexes.modulePushforwardCompModulePullbackIsoId`: `i^{-1}i_* =
  𝟭` on sheaves of modules.
* `Stacks.Cohomology.SupportedComplexes.derivedModulePushforwardCompModulePullbackIsoId`: the
  same on `D(𝒪_X|_Z)`.
* `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsIsoDerivedModulePullback`:
  **Stacks 0AEF, part (2)**, on `D_Z(𝒪_X)` the functor `RH_Z` agrees with `i^{-1}`.
* `closedSubsetDerivedPushforwardEquivalence_inverse_iso_derivedModulePullback`, in the same
  namespace: the quasi-inverse of the equivalence of part (2) is `i^{-1}` restricted to
  `D_Z(𝒪_X)`.

## Implementation notes

`modulePullback` is *defined* as the abstract left adjoint of `modulePushforward`, so nothing here
computes a section of `i^{-1}`: everything goes through the adjunction `i^{-1} ⊣ i_*`, whose counit
`i^{-1}i_*ℱ ⟶ ℱ` is invertible because `i_*` is fully faithful (Stacks 08KS,
`Stacks.SheafOfModules.SupportedSections.fullyFaithfulModulePushforwardClosedSubset`).  This is the
sheaf-of-modules counterpart of the sheaf-of-abelian-groups statement
`ClosedImmersionSheaves.sheaf_pullback_pushforward_counit_isIso` (Modules 01AX).

## References

* [Stacks Project, Lemma 20.34.4 (Tag 0AEF)](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Lemma 17.6.2 (Tag 08KS)](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-! ### A quasi-inverse pair of exact functors on derived categories -/

/-- For exact functors `F : C₁ ⥤ C₂` and `G : C₂ ⥤ C₁` with `F ⋙ G ≅ 𝟭 C₁`, the functors they
induce on unbounded derived categories again compose to the identity. -/
def exactFunctorDerivedCompIsoId
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₁) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ⋙ G ≅ 𝟭 C₁) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 (DerivedCategory C₁) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C₁)) _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

/-! ### `i^{-1} i_* = 𝟭` on sheaves of modules and on the derived category -/

/-- Inverse image undoes pushforward from a closed subset: the counit `i^{-1}i_*ℱ ⟶ ℱ` of the
adjunction `i^{-1} ⊣ i_*` is an isomorphism.

This is the sheaf-of-modules form of the sheaf-of-abelian-groups statement
`ClosedImmersionSheaves.sheaf_pullback_pushforward_counit_isIso` (Modules 01AX). -/
@[sga "4 IV 14.3" "partial"]
alias modulePushforwardCompModulePullbackIsoId := closedSubsetPullbackPushforwardIso

/-- Inverse image undoes pushforward from a closed subset on unbounded derived categories:
`i^{-1} ∘ i_* ≅ 𝟭` on `D(𝒪_X|_Z)`. -/
def derivedModulePushforwardCompModulePullbackIsoId (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    (letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := preservesFiniteLimits_modulePullback_closedSubsetInclusion X Z
    letI := preservesFiniteColimits_modulePullback (closedSubsetInclusion X Z)
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
        (modulePullback (closedSubsetInclusion X Z)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (_root_.SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X Z))))) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := preservesFiniteLimits_modulePullback_closedSubsetInclusion X Z
  letI := preservesFiniteColimits_modulePullback (closedSubsetInclusion X Z)
  exactFunctorDerivedCompIsoId _ _ (modulePushforwardCompModulePullbackIsoId X Z hZ)

/-! ### Part (2): on `D_Z(𝒪_X)` the functor `RH_Z` is `i^{-1}` -/

/-- On the full subcategory `D_Z(𝒪_X)` of complexes with cohomology sheaves supported on the closed
subset `Z`, the right derived functor `RH_Z` of sections supported on `Z` agrees with inverse image
`i^{-1}` along the inclusion. -/
@[stacks 0AEF "part (2): on D_Z the quasi-inverse RℋZ agrees with i⁻¹"]
def derivedSupportedSectionsIsoDerivedModulePullback (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    (letI := preservesFiniteLimits_modulePullback_closedSubsetInclusion X Z
    letI := preservesFiniteColimits_modulePullback (closedSubsetInclusion X Z)
    (supportedDerivedProperty X Z).ι ⋙ derivedSupportedSectionsOnClosed X Z hZ ≅
      (supportedDerivedProperty X Z).ι ⋙
        (modulePullback (closedSubsetInclusion X Z)).mapDerivedCategory) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := preservesFiniteLimits_modulePullback_closedSubsetInclusion X Z
  letI := preservesFiniteColimits_modulePullback (closedSubsetInclusion X Z)
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _
      (derivedModulePushforwardCompModulePullbackIsoId X Z hZ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (iotaIsoCompOfCounitIso (derivedPushforwardAdjunction X Z hZ)
        (supportedDerivedProperty X Z)
        (isIso_derivedPushforwardAdjunction_counit_app_of_supported X Z hZ))
      (modulePullback (closedSubsetInclusion X Z)).mapDerivedCategory

/-- The quasi-inverse of the equivalence `i_*^D : D(𝒪_X|_Z) ≌ D_Z(𝒪_X)` is inverse image `i^{-1}`
restricted to `D_Z(𝒪_X)`. -/
@[stacks 0AEF "part (2): the quasi-inverse is i⁻¹ restricted to D_Z"]
def closedSubsetDerivedPushforwardEquivalence_inverse_iso_derivedModulePullback
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) :
    (letI := preservesFiniteLimits_modulePullback_closedSubsetInclusion X Z
    letI := preservesFiniteColimits_modulePullback (closedSubsetInclusion X Z)
    (closedSubsetDerivedPushforwardEquivalence X Z hZ).inverse ≅
      (supportedDerivedProperty X Z).ι ⋙
        (modulePullback (closedSubsetInclusion X Z)).mapDerivedCategory) :=
  letI := preservesFiniteLimits_modulePullback_closedSubsetInclusion X Z
  letI := preservesFiniteColimits_modulePullback (closedSubsetInclusion X Z)
  closedSubsetDerivedPushforwardEquivalence_inverse X Z hZ ≪≫
    derivedSupportedSectionsIsoDerivedModulePullback X Z hZ

end Stacks.Cohomology.SupportedComplexes

end
