module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySpellingBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsSheafTriangle
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.SupportedSectionsOnClosed

/-!
# The abelian counterpart of the counit of Stacks 0G72

Let `Z` be a closed subset of a ringed space `X` and `i : Z ⟶ X` the inclusion.  On sheaves of
`𝒪_X`-modules the library has the canonical map

`i_* R𝓗_Z(K) ⟶ K`

of [Stacks, Tag 0G72] — `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsToId`, whose
value at the chosen derived functor is `Stacks.Perfect.SupportedFraction.supportPushCounit`, out of
which the comparison of [Stacks, Tag 0G7L] is built.  On sheaves of **abelian groups** it had no
such map: the abelian derived functor
`Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed` lands on `Z` and is
never composed back with `i_*`, and underived there was only the adjunction `i_* ⊣ ℋ_Z` of
[Stacks, Tag 01AZ], built from a hom-set bijection, whose counit is not named and whose naturality
lemma `ClosedImmersionSheaves.supportedSectionsSheafι_naturality` is `private`.

This file supplies the abelian map, and the underived half of its compatibility with the forgetful
functor.

## Main definitions

* `abelianSupportedSectionsToId`: **the underived abelian counit** `i_*ℋ_Z(F) ⟶ F`, assembled as a
  genuine natural transformation into the identity functor of `Ab(X)`.
* `abelianHomotopyIdentityIso` and `abelianIdentityIsRightDerivedFunctor`: the identity functor of
  `D(Ab(X))` as a right derived functor of the identity applied degreewise, the abelian counterpart
  of `Stacks.Cohomology.RestrictionCover.homotopyIdentityIso` and of
  `Stacks.Cohomology.SupportedComplexes.identityIsRightDerivedFunctorOfMapHomotopy`.
* `derivedAbelianSupportedSectionsToId`: **the derived abelian counit** `i_* R𝓗_Z^{ab}(K) ⟶ K`, for
  an arbitrary right derived functor of the abelian supported-sections endofunctor.
* `derivedAbelianSupportedPushforward`, with `derivedAbelianSupportedPushforwardSplit`,
  `derivedAbelianSupportedPushforwardUnit` and
  `derivedAbelianSupportedPushforward_isRightDerivedFunctor`: the canonical abelian
  `i_* R𝓗_Z^{ab} : D(Ab(X)) ⥤ D(Ab(X))`, namely
  `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed` composed with the
  exact direct image from `Z`, exhibited as a right derived functor of `F ↦ i_*ℋ_Z(F)`.
* `abelianSupportPushCounit`: the counit at that canonical choice, the abelian counterpart of
  `Stacks.Perfect.SupportedFraction.supportPushCounit`, with no hypothesis beyond `IsClosed Z`.
* `abelianSupportedSectionsForgetIso`, `forgetfulSupportedEndoUnit`,
  `abelianSupportedEndoForgetUnit` and `abelianSupportedEndoForgetComparison`: the comparison of
  [Stacks, Tag 0G74] part (2) **with `i_*` folded in**, as a map `(i_* R𝓗_Z(K))_ab ⟶
  i_* R𝓗_Z^{ab}(K_ab)` of endofunctors of the derived categories, with its characterising
  factorisation `abelianSupportedEndoForgetComparison_fac`.

## Main results

* `abelianSupportedSectionsSheafι_naturality`: the naturality of the subsheaf inclusion, restated
  here because the library's version is `private`.
* `adjunction_counit_eq`: **the underived abelian counit is the counit of the adjunction of
  [Stacks, Tag 01AZ]**, read through
  `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_comp_pushforward_iso`.  This is what
  identifies the transformation assembled here with the one the adjunction already contained but
  did not name.
* `abelianSupportedSectionsForgetIso_hom_comp_toId`: **the underived compatibility of the counit
  with the forgetful functor** — forgetting the module structure carries the inclusion
  `i_*ℋ_Z(ℱ) ⟶ ℱ` of `𝒪_X`-module sections supported on `Z` to the inclusion
  `i_*ℋ_Z(ℱ_ab) ⟶ ℱ_ab` of abelian ones, under
  `Stacks.Cohomology.SupportedComplexes.supportedSectionsSheafForgetIso`.
* `isRightDerivedFunctor_forgetfulSupportedEndoUnit`: forgetting the module structure is exact, so
  it carries a right derived functor of `ℱ ↦ i_*ℋ_Z(ℱ)` to one again.

## Implementation notes

**Carried hypotheses.**  Everything in this file carries at most `hZ : IsClosed Z`, together with
the standing size conditions that instance search discharges.  `abelianSupportedSectionsToId`,
`abelianSupportedSectionsSheafι_naturality`, `abelianHomotopyIdentityIso`,
`abelianIdentityIsRightDerivedFunctor`, `derivedAbelianSupportedSectionsToId` and its `_fac`,
`abelianSupportedSectionsForgetIso` and `abelianSupportedSectionsForgetIso_hom_comp_toId` need **no
closedness hypothesis at all**; `hZ` enters only where the realization of supported sections on `Z`
or the exactness of `i_*` is used, that is from
`abelianClosedPushforward_preservesFiniteLimits` onwards and in `adjunction_counit_eq`.  In
particular **no quasi-coherence and no hypothesis on the coefficient sheaf appears anywhere.**  The
declarations in the `Forget` section quantify over arbitrary right derived functors `RH` of
`ℱ ↦ i_*ℋ_Z(ℱ)` on `𝒪_X`-modules and `RHab` of `F ↦ i_*ℋ_Z(F)` on abelian sheaves, with their
derivation units, exactly as
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison` does.

**Two spellings of the abelian sheaf category.**  `ClosedImmersionSheaves.supportedSectionsFunctor`
is stated with source and target `X.carrier.Sheaf AddCommGrpCat`, whereas the derived-category
machinery of this tree works with `Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat`.
These are the same category, but instance search does not see through the difference: with the
first spelling neither the additivity instance nor `DerivedCategory.Qh.IsLocalization` is found.
Everything here is therefore written with the respelled abbreviations
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSections`,
`abelianSupportedSectionsOnClosed` and `abelianClosedPushforward`, which is why
`abelianSupportedSectionsForgetIso` is `supportedSectionsSheafForgetIso` re-exported `by exact`.

**What is NOT reached: the derived compatibility.**  The remaining statement, that the module
counit becomes the abelian counit after forgetting, i.e. that

`whiskerRight (derivedSupportedSectionsToId X Z RH aH)
  (underlyingDerivedSheaf (structureSheafRing X))`

equals `abelianSupportedEndoForgetComparison` followed by
`whiskerLeft (underlyingDerivedSheaf (structureSheafRing X))
  (derivedAbelianSupportedSectionsToId X Z RHab aHab)`
(both read as maps `RH ⋙ Φ ⟶ Φ` through the unitors), **is not proved here and is not assumed
here**.  The reduction of it is complete: by `CategoryTheory.Functor.rightDerived_ext` applied to
`forgetfulSupportedEndoUnit`, together with `derivedSupportedSectionsToId_fac`,
`derivedAbelianSupportedSectionsToId_fac`, `abelianSupportedEndoForgetComparison_fac`, the
naturality of the derived abelian counit and the naturality of
`(SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh`, every derived functor
cancels and the claim becomes the single identity **in the homotopy category of abelian sheaves**

`(toSheaf 𝒪_X).mapHomotopyCategory c |>.map
    ((NatTrans.mapHomotopyCategory (supportedSectionsSubsheafInclusion X Z) c).app K ≫
      (homotopyIdentityIso (structureSheafRing X)).hom.app K)`
` = (Functor.mapHomotopyCategoryCompIso (abelianSupportedSectionsForgetIso X Z) c).hom.app K ≫`
`   (Functor.mapHomotopyCategoryCompIso (Iso.refl (toSheaf 𝒪_X ⋙ abelianSupportedSections Z))
      c).inv.app K ≫`
`   (NatTrans.mapHomotopyCategory (abelianSupportedSectionsToId X Z) c).app
      ((toSheaf 𝒪_X).mapHomotopyCategory c |>.obj K) ≫`
`   (abelianHomotopyIdentityIso X).hom.app ((toSheaf 𝒪_X).mapHomotopyCategory c |>.obj K)`,

which is exactly `abelianSupportedSectionsForgetIso_hom_comp_toId` transported along
`NatTrans.mapHomotopyCategory`.  That last transport is where the work stopped: the terms involved
are large enough that closing it exceeds the default heartbeat limit, and raising the limit with
`set_option` was not permitted.  Consequently **nothing here proves the non-`𝒪_X`-linear comparison
square of step (ii) of [Stacks, Tag 0G85], and nothing here assumes any part of it.**

Also not reached: the invertibility of `abelianSupportedEndoForgetComparison` (the analogue, with
`i_*` folded in, of
`isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor`); any identification of
`abelianSupportPushCounit` with the counit of a derived adjunction; the naturality in a merely
additive morphism of the augmentation of [Stacks, Tag 0G7L]; and any statement about the Čech
cokernel of [Stacks, Tag 0G7Q], which is nowhere mentioned in this file.

**No declaration here carries a `@[stacks ...]` attribute.**

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 17.5.6 (Tag 01AZ)](https://stacks.math.columbia.edu/tag/01AZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.SheafOfModules (supportedSectionsSheafι)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.SheafOfModules.SupportedSections
open Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport (AbelianSheavesOnSpace
  hasRightDerivedFunctor_abelianSheaves)

universe u

namespace Stacks.Cohomology.AbelianSupportedCounit

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.abelianSheaves_isGrothendieckAbelian

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-! ### The underived counit -/

/-- The inclusion of the subsheaf of sections supported on `Z` is natural in the abelian sheaf.

This restates `ClosedImmersionSheaves.supportedSectionsSheafι_naturality`, which is `private` in
`StacksFrontier.Topology.Sheaves.ClosedImmersion.SupportedSectionsOnClosed`; the proof is the same
one, both subsheaves being cut out of the ambient sections and the map being the identity on
them. -/
public theorem abelianSupportedSectionsSheafι_naturality
    {F G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}} (f : F ⟶ G) :
    (abelianSupportedSections Z).map f ≫ supportedSectionsSheafι Z G =
      supportedSectionsSheafι Z F ≫ f := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  rfl

/-- **The underived abelian counit `i_*ℋ_Z(F) ⟶ F`**, as a natural transformation into the
identity functor of abelian sheaves on `X`.

This is the abelian counterpart of
`Stacks.Cohomology.SupportedComplexes.supportedSectionsSubsheafInclusion`.  The library had the
components — `AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι` — and the naturality only
as a `private` lemma, so the transformation itself was never assembled. -/
public def abelianSupportedSectionsToId :
    abelianSupportedSections Z ⟶
      Functor.id (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) where
  app F := supportedSectionsSheafι Z F
  naturality _ _ f := abelianSupportedSectionsSheafι_naturality X Z f

/-! ### The identity functor as a right derived functor -/

/-- Applying the identity functor of abelian sheaves degreewise is canonically isomorphic to the
identity functor of the homotopy category.  This is the abelian counterpart of
`Stacks.Cohomology.RestrictionCover.homotopyIdentityIso`. -/
public def abelianHomotopyIdentityIso :
    (Functor.id
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})).mapHomotopyCategory
        (ComplexShape.up ℤ) ≅
      Functor.id (HomotopyCategory
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))
      (HomotopyCategory.quotient
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ)))

/-- The identity functor of the derived category of abelian sheaves is a right derived functor of
the identity functor applied degreewise: the comparison is invertible, so nothing is derived. -/
public instance abelianIdentityIsRightDerivedFunctor :
    (Functor.id (DerivedCategory
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))).IsRightDerivedFunctor
      (Functor.whiskerRight (abelianHomotopyIdentityIso X).hom DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ (Functor.id _)
    (Functor.isoWhiskerRight (abelianHomotopyIdentityIso X).symm DerivedCategory.Qh)

/-! ### The derived abelian counit -/

/-- **The canonical map `i_* R𝓗_Z^{ab}(K) ⟶ K`**, for an arbitrary right derived functor `RHab`
of the abelian supported-sections endofunctor `F ↦ i_*ℋ_Z(F)` with derivation unit `aHab`.

This is the abelian counterpart of
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsToId`, and is built the same way:
the underived counit is derived through the universal property of `RHab`, the identity functor of
the derived category being a right derived functor of the identity. -/
public def derivedAbelianSupportedSectionsToId
    (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))
    (aHab : (abelianSupportedSections Z).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))] :
    RHab ⟶ Functor.id
      (DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})) :=
  Functor.rightDerivedNatTrans RHab (Functor.id _) aHab
    (Functor.whiskerRight (abelianHomotopyIdentityIso X).hom DerivedCategory.Qh)
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (abelianSupportedSectionsToId X Z) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The derived abelian counit is determined by its composite with the derivation units: it is
the unique transformation extending the underived counit. -/
public lemma derivedAbelianSupportedSectionsToId_fac
    (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))
    (aHab : (abelianSupportedSections Z).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))] :
    aHab ≫ Functor.whiskerLeft DerivedCategory.Qh
        (derivedAbelianSupportedSectionsToId X Z RHab aHab) =
      Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (abelianSupportedSectionsToId X Z) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫
        Functor.whiskerRight (abelianHomotopyIdentityIso X).hom DerivedCategory.Qh :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-! ### The canonical abelian `i_* R𝓗_Z` and its counit -/

include hZ in
/-- The direct image of abelian sheaves along the inclusion of the closed subset `Z` preserves
finite limits, being exact (Stacks 01AX). -/
public lemma abelianClosedPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (abelianClosedPushforward Z) :=
  (Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward
    (ClosedImmersionSheaves.closedSubsetInclusion Z) hZ.isClosedEmbedding_subtypeVal).1

include hZ in
/-- The direct image of abelian sheaves along the inclusion of the closed subset `Z` preserves
finite colimits, being exact (Stacks 01AX). -/
public lemma abelianClosedPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (abelianClosedPushforward Z) :=
  (Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward
    (ClosedImmersionSheaves.closedSubsetInclusion Z) hZ.isClosedEmbedding_subtypeVal).2

include hZ in
/-- **`i_* R𝓗_Z^{ab} : D(Ab(X)) ⥤ D(Ab(X))`**, the canonical derived functor of the sections of
an abelian sheaf supported on the closed subset `Z`, followed by the direct image from `Z`.

The direct image is exact, so it needs no deriving and is applied through
`CategoryTheory.Functor.mapDerivedCategory`.  This is the abelian counterpart of
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward`, built from the canonical
`Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed`, which the library
had but never composed back with `i_*`. -/
public def derivedAbelianSupportedPushforward :
    DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
  letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  derivedAbelianSupportedSectionsOnClosed X Z hZ ⋙
    (abelianClosedPushforward Z).mapDerivedCategory

/-- Splitting off the exact factor: on homotopy categories, `F ↦ i_*ℋ_Z(F)` followed by
localization is `ℋ_Z` followed by localization, followed by the direct image read on derived
categories.  The first step is
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRealizedCompPushforwardIso`, the
second the invertible comparison of the exact direct image. -/
public def derivedAbelianSupportedPushforwardSplit :
    letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
    letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
    (abelianSupportedSections Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ≅
      ((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⋙ (abelianClosedPushforward Z).mapDerivedCategory :=
  letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ)
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      (abelianClosedPushforward Z).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The canonical comparison exhibiting `i_* R𝓗_Z^{ab}` as a right derived functor of
`F ↦ i_*ℋ_Z(F)`: the derivation unit of `R𝓗_Z^{ab}`, pushed forward, after the invertible
reassociation that splits off the exact direct image. -/
public def derivedAbelianSupportedPushforwardUnit :
    (abelianSupportedSections Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedAbelianSupportedPushforward X Z hZ :=
  letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  (derivedAbelianSupportedPushforwardSplit X Z hZ).hom ≫
    Functor.whiskerRight (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
      (abelianClosedPushforward Z).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- `i_* R𝓗_Z^{ab}` is a right derived functor of `F ↦ i_*ℋ_Z(F)`: the comparison is invertible
at a K-injective complex, where the derivation unit of `R𝓗_Z^{ab}` already is. -/
public instance derivedAbelianSupportedPushforward_isRightDerivedFunctor :
    (derivedAbelianSupportedPushforward X Z hZ).IsRightDerivedFunctor
      (derivedAbelianSupportedPushforwardUnit X Z hZ)
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) := by
  have := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  have := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => ?_
  have hunit : IsIso ((derivedAbelianSupportedSectionsOnClosedUnit X Z hZ).app
      ((HomotopyCategory.quotient
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I
  have hsplit : IsIso ((derivedAbelianSupportedPushforwardSplit X Z hZ).hom.app
      ((HomotopyCategory.quotient
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj I)) := inferInstance
  have hassoc : IsIso ((Functor.associator DerivedCategory.Qh
      (derivedAbelianSupportedSectionsOnClosed X Z hZ)
      (abelianClosedPushforward Z).mapDerivedCategory).hom.app
      ((HomotopyCategory.quotient
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj I)) := inferInstance
  have hmid : IsIso ((Functor.whiskerRight (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
      (abelianClosedPushforward Z).mapDerivedCategory).app
      ((HomotopyCategory.quotient
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj I)) :=
    Functor.map_isIso _ _
  dsimp only [derivedAbelianSupportedPushforwardUnit]
  simp only [NatTrans.comp_app]
  exact IsIso.comp_isIso' hsplit (IsIso.comp_isIso' hmid hassoc)

/-- **The abelian counit `i_* R𝓗_Z^{ab}(K) ⟶ K`, with no hypothesis beyond `hZ`.**  This is the
abelian counterpart of `Stacks.Perfect.SupportedFraction.supportPushCounit`, the canonical map of
[Stacks, Tag 0G72] on the derived category of `𝒪_X`-modules, at the canonical abelian derived
functor built above. -/
public abbrev abelianSupportPushCounit :
    derivedAbelianSupportedPushforward X Z hZ ⟶
      Functor.id
        (DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})) :=
  derivedAbelianSupportedSectionsToId X Z (derivedAbelianSupportedPushforward X Z hZ)
    (derivedAbelianSupportedPushforwardUnit X Z hZ)

/-! ### Compatibility of the counit with the forgetful functor -/

/-- Forgetting the module structure and then taking abelian supported sections on `Z` is
additive. -/
public instance forget_abelianSupportedSections_additive :
    (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianSupportedSections Z).Additive :=
  inferInstance

/-- **Forgetting the module structure commutes with `ℱ ↦ i_*ℋ_Z(ℱ)`**, in the spelling in which
the target is the respelled abelian supported-sections endofunctor.  This is
`Stacks.Cohomology.SupportedComplexes.supportedSectionsSheafForgetIso`; only the spelling of the
abelian sheaf category differs. -/
public def abelianSupportedSectionsForgetIso :
    supportedSectionsFunctor X Z ⋙ _root_.SheafOfModules.toSheaf (structureSheafRing X) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianSupportedSections Z := by
  exact supportedSectionsSheafForgetIso X Z

/-- **The underived compatibility: the module counit becomes the abelian counit.**  Forgetting
the module structure carries the inclusion `i_*ℋ_Z(ℱ) ⟶ ℱ` of the subsheaf of `𝒪_X`-module
sections supported on `Z` to the inclusion `i_*ℋ_Z(ℱ_ab) ⟶ ℱ_ab` of the abelian one, under the
identification `abelianSupportedSectionsForgetIso`.

Both sides are, on sections over an open set, the inclusion of the subgroup of sections supported
on `Z` into the ambient sections, so the identification is sectionwise the identity and the claim
holds by `rfl` at each component. -/
public theorem abelianSupportedSectionsForgetIso_hom_comp_toId :
    (abelianSupportedSectionsForgetIso X Z).hom ≫
        Functor.whiskerLeft (_root_.SheafOfModules.toSheaf (structureSheafRing X))
          (abelianSupportedSectionsToId X Z) =
      Functor.whiskerRight (supportedSectionsSubsheafInclusion X Z)
        (_root_.SheafOfModules.toSheaf (structureSheafRing X)) := by
  ext F
  rfl

include hZ in
/-- **The underived abelian counit is the counit of the adjunction of [Stacks, Tag 01AZ].**  The
adjunction `i_* ⊣ ℋ_Z` of
`ClosedImmersionSheaves.closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction` is
built from a hom-set bijection and so has no named counit; its counit is the transformation
assembled above, read through the identification
`ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_comp_pushforward_iso` of `i_*ℋ_Z` with the
supported-sections subsheaf. -/
public theorem adjunction_counit_eq :
    (ClosedImmersionSheaves.closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction
        Z hZ).counit =
      (ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_comp_pushforward_iso Z hZ).hom ≫
        abelianSupportedSectionsToId X Z := by
  ext F
  simp only [
    ClosedImmersionSheaves.closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction,
    Adjunction.mkOfHomEquiv_counit_app]
  rfl

section Forget

variable
  (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))
  (aHab : (abelianSupportedSections Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
  (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
  (aH : (supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)

/-- The derivation unit of a right derived functor of `ℱ ↦ i_*ℋ_Z(ℱ)` on `𝒪_X`-modules, composed
with forgetting the module structure.  This is the endofunctor analogue of
`Stacks.Cohomology.SupportedComplexes.forgetfulSupportedSheafUnit`. -/
public def forgetfulSupportedEndoUnit :
    ((supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ underlyingDerivedSheaf (structureSheafRing X) ⟶
      DerivedCategory.Qh ⋙ (RH ⋙ underlyingDerivedSheaf (structureSheafRing X)) :=
  Functor.whiskerRight aH (underlyingDerivedSheaf (structureSheafRing X)) ≫
    (Functor.associator _ _ _).hom

/-- Forgetting the module structure is exact, so it carries a right derived functor of
`ℱ ↦ i_*ℋ_Z(ℱ)` to one again. -/
public instance isRightDerivedFunctor_forgetfulSupportedEndoUnit
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    (RH ⋙ underlyingDerivedSheaf (structureSheafRing X)).IsRightDerivedFunctor
      (forgetfulSupportedEndoUnit X Z RH aH)
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I _ => ?_)
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RH aH I
  dsimp only [forgetfulSupportedEndoUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app]
  infer_instance

/-- The comparison on homotopy categories built from the underived forgetful comparison of
supported sections and the derivation unit of a right derived functor of abelian supported
sections.  This is the endofunctor analogue of
`Stacks.Cohomology.SupportedComplexes.supportedSheafForgetUnit`. -/
public def abelianSupportedEndoForgetUnit :
    ((supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ underlyingDerivedSheaf (structureSheafRing X) ⟶
      DerivedCategory.Qh ⋙ (underlyingDerivedSheaf (structureSheafRing X) ⋙ RHab) :=
  Functor.whiskerLeft
      ((supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ))
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator
      ((supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ))
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      DerivedCategory.Qh).inv ≫
    Functor.whiskerRight
      (@Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
        (abelianSupportedSectionsForgetIso X Z)
        (by exact supportedSectionsFunctor_additive_endo X Z)
        (by exact inferInstanceAs (_root_.SheafOfModules.toSheaf (structureSheafRing X)).Additive)
        (by exact forget_abelianSupportedSections_additive X Z)
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerRight
      (@Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
        (Iso.refl
          (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianSupportedSections Z))
        (by exact inferInstanceAs (_root_.SheafOfModules.toSheaf (structureSheafRing X)).Additive)
        (by exact abelianSupportedSections_additive Z)
        (by exact forget_abelianSupportedSections_additive X Z)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      ((abelianSupportedSections Z).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
        (ComplexShape.up ℤ)) aHab ≫
    Functor.whiskerRight
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.inv RHab

/-- **The comparison of [Stacks, Tag 0G74] part (2) with `i_*` folded in**: the canonical map
`(i_* R𝓗_Z(K))_ab ⟶ i_* R𝓗_Z^{ab}(K_ab)` of endofunctors of the derived categories, induced
through the universal property of `RH` by the underived forgetful comparison.

This is the endofunctor analogue of
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison`, which is stated on
`Z` with no direct image applied and therefore cannot be composed with the counit. -/
public def abelianSupportedEndoForgetComparison
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    RH ⋙ underlyingDerivedSheaf (structureSheafRing X) ⟶
      underlyingDerivedSheaf (structureSheafRing X) ⋙ RHab :=
  (RH ⋙ underlyingDerivedSheaf (structureSheafRing X)).rightDerivedDesc
    (forgetfulSupportedEndoUnit X Z RH aH)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))
    _ (abelianSupportedEndoForgetUnit X Z RHab aHab)

/-- The comparison is pinned down by its composite with the derivation unit of `RH`. -/
public lemma abelianSupportedEndoForgetComparison_fac
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    forgetfulSupportedEndoUnit X Z RH aH ≫ Functor.whiskerLeft DerivedCategory.Qh
        (abelianSupportedEndoForgetComparison X Z RHab aHab RH aH) =
      abelianSupportedEndoForgetUnit X Z RHab aHab :=
  Functor.rightDerived_fac _ _ _ _ _

end Forget

end Stacks.Cohomology.AbelianSupportedCounit

end
