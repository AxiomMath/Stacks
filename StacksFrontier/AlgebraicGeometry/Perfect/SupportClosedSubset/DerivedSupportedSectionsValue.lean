module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedFunctorAtKInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsSheafTriangle

/-!
# Derived sections with support computed on a K-injective complex

Let `Z` be a closed subset of a ringed space `X`, let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the
inclusion and let `Rℋ_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)` be the chosen total right derived functor of
sections supported on `Z`.  On a K-injective complex `ℐ^•` of `𝒪_X`-modules the derived functor
is computed degreewise, and pushing the result forward to `X` turns it into the subcomplex of
sections supported on `Z`:

`i_* Rℋ_Z(ℐ^•) ≅ ℋ_Z(ℐ^•)` in `D(𝒪_X)`.

Since `i_*` is exact and fully faithful, a cohomology sheaf of `Rℋ_Z(ℐ^•)` vanishes exactly
when the corresponding cohomology sheaf of the complex `ℋ_Z(ℐ^•)` does.  This reduces every
vanishing statement about `ℋ^i_Z` to a statement about an explicit complex of sheaves on `X`.

## Main definitions

* `pushforwardDerivedSupportedSectionsIso`: the isomorphism `i_* Rℋ_Z(ℐ^•) ≅ ℋ_Z(ℐ^•)`.

## Main results

* `isZero_of_isZero_modulePushforward`: an `𝒪_X|_Z`-module whose pushforward to `X` vanishes
  vanishes.
* `isZero_homology_derivedSupportedSections_of_isZero` and
  `isZero_homology_supportedSectionsComplex_of_isZero`: the degree-`i` cohomology sheaf of the
  complex `ℋ_Z(ℐ^•)` vanishes if and only if `ℋ^i_Z` of the object `ℐ^•` represents does.

## Implementation notes

The three isomorphisms composed in `pushforwardDerivedSupportedSectionsIso` are: the degreewise
computation of a right derived functor at a K-injective complex
(`Stacks.Perfect.KInjectiveValues.objIsoOfKInjective`, with the K-injective resolutions of
`Mod(𝒪_X)` supplied by
`Stacks.Cohomology.SupportedComplexes.exists_isKInjective_quasiIso_moduleSheaves`); the fact
that the exact functor `i_*` needs no deriving, which is
`CategoryTheory.Functor.mapDerivedCategoryFactors`; and the identification
`i_* ∘ ℋ_Z ≅ ℋ_Z` of Stacks 0G6N between the `𝒪_X|_Z`-valued functor of supported sections and
the subsheaf of sections supported on `Z`.

Reflecting the vanishing through `i_*` uses that `i_*` is fully faithful for a closed subset,
`Stacks.SheafOfModules.SupportedSections.fullyFaithfulModulePushforwardClosedSubset`, and that
it is exact, so that it commutes with the cohomology functors of the derived category by
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso`.

## References

* [Stacks Project, Tag 0G6N](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Perfect.DerivedSupportedSectionsValue

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **Derived sections with support, computed on a K-injective complex and pushed forward.**  For
a K-injective complex `ℐ^•` of `𝒪_X`-modules the object `i_* Rℋ_Z(ℐ^•)` of `D(𝒪_X)` is the
subcomplex `ℋ_Z(ℐ^•)` of sections supported on `Z`. -/
public def pushforwardDerivedSupportedSectionsIso
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hI : I.IsKInjective) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj
        ((derivedSupportedSectionsOnClosed X Z hZ).obj (DerivedCategory.Q.obj I)) ≅
      DerivedCategory.Q.obj
        (((supportedSectionsFunctor X Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.mapIso
      (Stacks.Perfect.KInjectiveValues.objIsoOfKInjective
        (supportedSectionsOnClosedFunctor X Z hZ) (derivedSupportedSectionsOnClosed X Z hZ)
        (derivedSupportedSectionsOnClosedUnit X Z hZ)
        (exists_isKInjective_quasiIso_moduleSheaves X) I hI) ≪≫
    (Functor.mapDerivedCategoryFactors
      (modulePushforward (closedSubsetInclusion X Z))).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
        (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ)
        (ComplexShape.up ℤ)).app I)

include hZ in
/-- **Pushforward along the inclusion of a closed subset reflects zero objects**, being fully
faithful. -/
public theorem isZero_of_isZero_modulePushforward
    (M : _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)))
    (h : IsZero ((modulePushforward (closedSubsetInclusion X Z)).obj M)) : IsZero M := by
  have := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).faithful
  refine (IsZero.iff_id_eq_zero _).2 (Functor.map_injective
    (modulePushforward (closedSubsetInclusion X Z)) ?_)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- The pushforward of the degree-`i` cohomology sheaf of `Rℋ_Z(ℐ^•)` vanishes if and only if the
degree-`i` cohomology sheaf of `ℋ_Z(ℐ^•)` does. -/
private theorem isZero_pushforward_homology_iff
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (i : ℤ) :
    IsZero ((modulePushforward (closedSubsetInclusion X Z)).obj
      ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) i).obj
      ((derivedSupportedSectionsOnClosed X Z hZ).obj (DerivedCategory.Q.obj I)))) ↔
    IsZero ((((supportedSectionsFunctor X Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology i) := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  exact Iso.isZero_iff (((exactFunctorDerivedHomologyIso
    (modulePushforward (closedSubsetInclusion X Z)) i).app
      ((derivedSupportedSectionsOnClosed X Z hZ).obj (DerivedCategory.Q.obj I))).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      (pushforwardDerivedSupportedSectionsIso X Z hZ I hI) ≪≫
    ((DerivedCategory.homologyFunctorFactors
      (_root_.SheafOfModules.{u} (structureSheafRing X)) i).app _))

/-- **A vanishing cohomology sheaf of the complex of supported sections is a vanishing local
cohomology sheaf.**  For a K-injective complex `ℐ^•`, if the degree-`i` cohomology sheaf of
`ℋ_Z(ℐ^•)` vanishes then the degree-`i` cohomology sheaf of `Rℋ_Z(ℐ^•)` vanishes. -/
public theorem isZero_homology_derivedSupportedSections_of_isZero
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (i : ℤ)
    (h : IsZero ((((supportedSectionsFunctor X Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology i)) :
    IsZero ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) i).obj
      ((derivedSupportedSectionsOnClosed X Z hZ).obj (DerivedCategory.Q.obj I))) :=
  isZero_of_isZero_modulePushforward X Z hZ _
    ((isZero_pushforward_homology_iff X Z hZ I hI i).2 h)

include hZ in
/-- **Conversely, a vanishing local cohomology sheaf is a vanishing cohomology sheaf of the
complex of supported sections.**  For a K-injective complex `ℐ^•`, if the degree-`i` cohomology
sheaf of `Rℋ_Z(ℐ^•)` vanishes then so does the degree-`i` cohomology sheaf of the complex
`ℋ_Z(ℐ^•)`. -/
public theorem isZero_homology_supportedSectionsComplex_of_isZero
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) i).obj
      ((derivedSupportedSectionsOnClosed X Z hZ).obj (DerivedCategory.Q.obj I)))) :
    IsZero ((((supportedSectionsFunctor X Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology i) :=
  (isZero_pushforward_homology_iff X Z hZ I hI i).1
    (Functor.map_isZero (modulePushforward (closedSubsetInclusion X Z)) h)

end Stacks.Perfect.DerivedSupportedSectionsValue

end
