module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.RingedSpace.DerivedPushforward
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent complexes with support in a closed subset

Let `X` be a scheme, let `T ⊆ X` be a closed subset whose open complement `U = X ∖ T` is
retrocompact, and let `i : T → X` be the inclusion.  Write `R𝓗_T : D(𝒪_X) ⥤ D(𝒪_X|_T)` for the
derived functor of sections supported on `T`.  This file proves Stacks 0G7G: the composite
`i_* ∘ R𝓗_T` carries `D_QCoh(𝒪_X)` into `D_{QCoh, T}(𝒪_X)`, and is there right adjoint to the
inclusion of `D_{QCoh, T}(𝒪_X)` in `D_QCoh(𝒪_X)`.

## Main definitions

* `derivedSupportedPushforward`: the functor `i_* R𝓗_T : D(𝒪_X) ⥤ D(𝒪_X)`, the chosen derived
  functor of sections supported on `T` followed by the exact direct image from `T`.
* `derivedRestrictPush`: the functor `Rj_*(-|_U) : D(𝒪_X) ⥤ D(𝒪_X)`, restriction to the open
  complement followed by the derived direct image.
* `quasiCoherentSupportedInclusion` and `quasiCoherentDerivedSupport`: the two functors between
  `D_{QCoh, T}(𝒪_X)` and `D_QCoh(𝒪_X)` that the adjunction of part (2) relates.

## Main results

* `quasiCoherentSupported_derivedSupportedPushforward`: **Stacks 0G7G (1)**.
* `quasiCoherentSupportedInclusionAdj`: **Stacks 0G7G (2)**, as an `Adjunction` term.
* `isIso_derivedSupportedSectionsToId_app_of_supported`: the counit `i_* R𝓗_T(A) ⟶ A` is
  invertible on complexes supported on `T`.

## Implementation notes

Both `i_* R𝓗_T` and `Rj_*(-|_U)` are produced as right derived functors of the two sheaf-level
functors appearing in the triangle of Stacks 0G72, so that triangle applies to them verbatim.
In each case one of the two factors is exact and therefore needs no deriving: the direct image
from a closed subset is exact by Stacks 08KS, and restriction to an open is exact because it
has adjoints on both sides.  The comparison transformation is accordingly the derivation unit
of the inexact factor flanked by two invertible reassociations, and it is invertible at a
K-injective complex because restriction preserves K-injectivity (Stacks 08BS).

Part (1) is the argument of the source.  In the triangle
`i_* R𝓗_T(E) ⟶ E ⟶ Rj_*(E|_U) ⟶ (i_* R𝓗_T(E))⟦1⟧` the middle term is quasi-coherent by
hypothesis and the right-hand term by Stacks 08D5, so the left-hand term is, `D_QCoh(𝒪_X)` being
a triangulated subcategory (Stacks 06UP applied to the weak Serre subcategory of Stacks 06VT).
Retrocompactness of `U` enters exactly once, as quasi-compactness of `j`, which is the
hypothesis of Stacks 08D5.  Support on `T` is separate and unconditional: it is Stacks 0AEF (1)
for the direct image from `T`.

Part (2) restricts the ambient adjunction `i_* ⊣ R𝓗_T` of Stacks 0A3B along two fully faithful
inclusions, using `CategoryTheory.Adjunction.restrictFullyFaithful`.  On the right that is the
inclusion of `D_QCoh(𝒪_X)` in `D(𝒪_X)`.  On the left it is `R𝓗_T` read on `D_{QCoh, T}(𝒪_X)`,
which is fully faithful because the counit `i_* R𝓗_T(A) ⟶ A` is invertible there — the
essential-image half of Stacks 0AEF, proved here from the same triangle: a complex supported on
`T` restricts to zero on `U`, so the third term of its triangle vanishes and the first map is an
isomorphism.

The derived category is the standard model throughout.  The locally small model arrives as a
global instance through the import of Stacks 08D5; see the comment on the priority attribute
below.

## References

* [Stacks Project, Lemma 36.6.4 (Tag 0G7G)](https://stacks.math.columbia.edu/tag/0G7G)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open Stacks.Cohomology.RestrictionCover
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Perfect.SupportedQuasicoherent

-- The locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` arrives
-- through the import of Stacks 08D5 as a *global* instance, and a global instance beats a
-- default-priority local one, so it would capture the unconstrained universe of an occurrence
-- of `DerivedCategory` here. Every library statement used below -- Stacks 08D5, Stacks 0A3B,
-- Stacks 0G72, Stacks 0AEF -- is elaborated at the standard model, so the standard model is
-- given a priority that wins.
attribute [local instance 10000] HasDerivedCategory.standard

section Restriction

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- Restriction of modules to an open subspace is additive: it has adjoints on both sides. -/
instance jStar_additive : (jStar U (structureSheafRing X)).Additive := by
  have : (jStar U (structureSheafRing X)).IsLeftAdjoint :=
    (jStarAdjunction U (structureSheafRing X)).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- Restriction of modules to an open subspace preserves finite limits, being a right
adjoint to extension by zero. -/
instance jStar_preservesFiniteLimits : PreservesFiniteLimits (jStar U (structureSheafRing X)) :=
  preservesFiniteLimits_jStar U (structureSheafRing X)

/-- Restriction of modules to an open subspace preserves finite colimits, being a left
adjoint to pushforward. -/
instance jStar_preservesFiniteColimits : PreservesFiniteColimits (jStar U (structureSheafRing X)) :=
  preservesFiniteColimits_jStar U (structureSheafRing X)

/-- Pushforward from an open subspace is additive, being a right adjoint to restriction. -/
instance jPush_additive : (jPush U (structureSheafRing X)).Additive := by
  have : (jPush U (structureSheafRing X)).IsRightAdjoint :=
    (jStarAdjunction U (structureSheafRing X)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- `Rj_*(-|_U) : D(𝒪_X) ⥤ D(𝒪_X)`, restriction to the open `U` followed by the derived
direct image along the inclusion of `U`.

Restriction is exact, so it needs no deriving; the derived direct image is
`AlgebraicGeometry.RingedSpace.derivedPushforward`. -/
def derivedRestrictPush :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (jStar U (structureSheafRing X)).mapDerivedCategory ⋙
    RingedSpace.derivedPushforward (X.ofRestrict U.isOpenEmbedding)

/-- Splitting off the exact factor: on homotopy categories, `ℱ ↦ j_*(ℱ|_U)` followed by
localization is restriction followed by the degreewise direct image into the derived
category. -/
def derivedRestrictPushSplit :
    (restrictPush (structureSheafRing X) U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ≅
      (jStar U (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        RingedSpace.pushforwardToDerivedCategory (X.ofRestrict U.isOpenEmbedding) :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (restrictPush (structureSheafRing X) U))
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- Moving the localization of the exact factor of restriction past it, which is possible
because the comparison `Functor.mapDerivedCategoryFactorsh` of an exact functor is
invertible. -/
def derivedRestrictPushReassoc :
    (jStar U (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh ⋙
          RingedSpace.derivedPushforward (X.ofRestrict U.isOpenEmbedding)) ≅
      DerivedCategory.Qh ⋙ derivedRestrictPush X U :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (jStar U (structureSheafRing X)).mapDerivedCategoryFactorsh.symm
      (RingedSpace.derivedPushforward (X.ofRestrict U.isOpenEmbedding)) ≪≫
    Functor.associator _ _ _

/-- The canonical comparison exhibiting `derivedRestrictPush` as a right derived functor of
`ℱ ↦ j_*(ℱ|_U)`: the derivation unit of the direct image, flanked by the two invertible
reassociations that split off the exact functor of restriction. -/
def derivedRestrictPushUnit :
    (restrictPush (structureSheafRing X) U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedRestrictPush X U :=
  (derivedRestrictPushSplit X U).hom ≫
    Functor.whiskerLeft ((jStar U (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ))
      (RingedSpace.derivedPushforwardUnit (X.ofRestrict U.isOpenEmbedding)) ≫
    (derivedRestrictPushReassoc X U).hom

/-- `Rj_*(-|_U)` is a right derived functor of `ℱ ↦ j_*(ℱ|_U)`: the comparison is invertible
at a K-injective complex `I`, because restriction preserves K-injectivity (Stacks 08BS), so
the derivation unit of the direct image is invertible at `I|_U`. -/
instance derivedRestrictPush_isRightDerivedFunctor :
    (derivedRestrictPush X U).IsRightDerivedFunctor (derivedRestrictPushUnit X U)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => ?_
  have hKI : CochainComplex.IsKInjective
      (((jStar U (structureSheafRing X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_jStar U (structureSheafRing X) I
  have hpush := RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective
    (X.ofRestrict U.isOpenEmbedding)
    (((jStar U (structureSheafRing X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) hKI
  have hsplit : IsIso ((derivedRestrictPushSplit X U).hom.app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) := inferInstance
  have hreassoc : IsIso ((derivedRestrictPushReassoc X U).hom.app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) := inferInstance
  have hmid : IsIso ((Functor.whiskerLeft
      ((jStar U (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ))
      (RingedSpace.derivedPushforwardUnit (X.ofRestrict U.isOpenEmbedding))).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) := hpush
  dsimp only [derivedRestrictPushUnit]
  simp only [NatTrans.comp_app]
  exact IsIso.comp_isIso' hsplit (IsIso.comp_isIso' hmid hreassoc)

end Restriction

section SupportedSections

variable (X : RingedSpace.{u, u}) (T : Set X.carrier) (hT : IsClosed T)

/-- Pushforward along the inclusion of a closed subset is additive, being a right adjoint to
the pullback of modules. -/
instance closedPushforward_additive :
    (modulePushforward (closedSubsetInclusion X T)).Additive := by
  let := pushforward_preservesFiniteLimits X T
  exact Functor.additive_of_preserves_binary_products _

/-- `i_* R𝓗_T : D(𝒪_X) ⥤ D(𝒪_X)`, the derived functor of sections supported on the closed
subset `T` followed by the direct image from `T`.

The direct image is exact, so it needs no deriving: it is applied through
`CategoryTheory.Functor.mapDerivedCategory`. -/
def derivedSupportedPushforward :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  letI := pushforward_preservesFiniteLimits X T
  letI := pushforward_preservesFiniteColimits X T hT
  derivedSupportedSectionsOnClosed X T hT ⋙
    (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory

/-- Splitting off the exact factor: on homotopy categories, `ℱ ↦ i_* ℋ_T(ℱ)` followed by
localization is `ℋ_T` followed by localization, followed by the direct image read on derived
categories. The first step is the identification
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` of Stacks 0G6N, the second the
invertible comparison of the exact direct image. -/
def derivedSupportedPushforwardSplit :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    (supportedSectionsFunctor X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ≅
      ((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⋙
        (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory :=
  letI := pushforward_preservesFiniteLimits X T
  letI := pushforward_preservesFiniteColimits X T hT
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory (ComplexShape.up ℤ))
      (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The canonical comparison exhibiting `i_* R𝓗_T` as a right derived functor of
`ℱ ↦ i_* ℋ_T(ℱ)`: the derivation unit of `R𝓗_T`, pushed forward, after the invertible
reassociation that splits off the exact direct image. -/
def derivedSupportedPushforwardUnit :
    (supportedSectionsFunctor X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSupportedPushforward X T hT :=
  letI := pushforward_preservesFiniteLimits X T
  letI := pushforward_preservesFiniteColimits X T hT
  (derivedSupportedPushforwardSplit X T hT).hom ≫
    Functor.whiskerRight (derivedSupportedSectionsOnClosedUnit X T hT)
      (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- `i_* R𝓗_T` is a right derived functor of `ℱ ↦ i_* ℋ_T(ℱ)`: the comparison is invertible
at a K-injective complex, where the derivation unit of `R𝓗_T` already is. -/
instance derivedSupportedPushforward_isRightDerivedFunctor :
    (derivedSupportedPushforward X T hT).IsRightDerivedFunctor
      (derivedSupportedPushforwardUnit X T hT)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  let := pushforward_preservesFiniteLimits X T
  let := pushforward_preservesFiniteColimits X T hT
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => ?_
  have hunit : IsIso ((derivedSupportedSectionsOnClosedUnit X T hT).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I
  have hsplit : IsIso ((derivedSupportedPushforwardSplit X T hT).hom.app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) := inferInstance
  have hassoc : IsIso ((Functor.associator DerivedCategory.Qh
      (derivedSupportedSectionsOnClosed X T hT)
      (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory).hom.app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) := inferInstance
  have hmid : IsIso ((Functor.whiskerRight (derivedSupportedSectionsOnClosedUnit X T hT)
      (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) :=
    Functor.map_isIso _ _
  dsimp only [derivedSupportedPushforwardUnit]
  simp only [NatTrans.comp_app]
  exact IsIso.comp_isIso' hsplit (IsIso.comp_isIso' hmid hassoc)

end SupportedSections

section Vanishing

/-- Alias of `Stacks.Cohomology.PushforwardRestriction.isZero_derived_of_homology_isZero`. -/
alias isZero_of_homology_isZero :=
  Stacks.Cohomology.PushforwardRestriction.isZero_derived_of_homology_isZero

/-- The derived direct image of a ringed space morphism kills a zero object: it is computed on
a K-injective resolution, and a K-injective resolution of a zero complex is acyclic, hence
null-homotopic, hence killed by the degreewise direct image. -/
theorem isZero_derivedPushforward_obj {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (hZ : IsZero Z) :
    IsZero ((RingedSpace.derivedPushforward f).obj Z) := by
  let : (modulePushforward f).IsRightAdjoint :=
    (modulePullbackPushforwardAdjunction f).isRightAdjoint
  let : (modulePushforward f).Additive := Functor.additive_of_preserves_binary_products _
  have : (RingedSpace.pushforwardToDerivedCategory f).Additive :=
    inferInstanceAs (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).Additive)
  obtain ⟨O₀, hO₀⟩ := (inferInstance :
    HasZeroObject (CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)).zero
  obtain ⟨J, q, hJ, hq⟩ := exists_isKInjective_quasiIso_moduleSheaves X O₀
  have := hJ
  have := hq
  have hJac : J.Acyclic := by
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hiso : IsIso (HomologicalComplex.homologyMap q n) :=
      (quasiIsoAt_iff_isIso_homologyMap q n).1 (hq.quasiIsoAt n)
    exact (Functor.map_isZero
      (HomologicalComplex.homologyFunctor (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ) n) hO₀).of_iso
      (asIso (HomologicalComplex.homologyMap q n)).symm
  have hhom : Homotopy (𝟙 J) 0 := CochainComplex.IsKInjective.homotopyZero (𝟙 J) hJac
  have hJzero : IsZero ((HomotopyCategory.quotient
      (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)).obj J) := by
    rw [IsZero.iff_id_eq_zero]
    have h1 : (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).map (𝟙 J) =
        (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).map 0 :=
      HomotopyCategory.eq_of_homotopy _ _ hhom
    simpa using h1
  have hunit := RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective f J hJ
  exact ((Functor.map_isZero (RingedSpace.pushforwardToDerivedCategory f) hJzero).of_iso
    (asIso ((RingedSpace.derivedPushforwardUnit f).app _)).symm).of_iso
    ((RingedSpace.derivedPushforward f).mapIso
      (hZ.iso (Functor.map_isZero DerivedCategory.Qh hJzero)))

/-- A complex supported on the closed subset `T` restricts to zero on the open complement,
hence has zero derived restriction-pushforward `Rj_*(-|_U)`. -/
theorem isZero_derivedRestrictPush_of_supported (X : RingedSpace.{u, u}) (T : Set X.carrier)
    (hT : IsClosed T) (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hA : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) T A) :
    IsZero ((derivedRestrictPush X (openComplement T hT)).obj A) := by
  have hres :
      IsZero ((jStar (openComplement T hT) (structureSheafRing X)).mapDerivedCategory.obj A) := by
    refine isZero_of_homology_isZero _ fun n => ?_
    refine IsZero.of_iso ?_
      ((exactFunctorDerivedHomologyIso (jStar (openComplement T hT) (structureSheafRing X)) n).app
        A)
    exact Stacks.Cohomology.PushforwardRestriction.isZero_jStar_obj_of_stalk_isZero
      (structureSheafRing X) (openComplement T hT) _ fun x hx => hA n x hx
  exact isZero_derivedPushforward_obj (X.ofRestrict (openComplement T hT).isOpenEmbedding)
    ((jStar (openComplement T hT) (structureSheafRing X)).mapDerivedCategory.obj A) hres

/-- **The counit `i_* R𝓗_T(A) ⟶ A` is invertible on complexes supported on `T`.** In the
triangle of Stacks 0G72 the third term is `Rj_*(A|_U)`, which vanishes for such an `A`, so the
first map is an isomorphism. This is the essential-image half of Stacks 0AEF: every complex
supported on `T` is a direct image from `T`. -/
theorem isIso_derivedSupportedSectionsToId_app_of_supported (X : RingedSpace.{u, u})
    (T : Set X.carrier) (hT : IsClosed T)
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hA : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) T A) :
    IsIso ((derivedSupportedSectionsToId X T (derivedSupportedPushforward X T hT)
      (derivedSupportedPushforwardUnit X T hT)).app A) :=
  (Triangle.isZero₃_iff_isIso₁ _
    (derivedSupportedSectionsTriangle_distinguished X T hT
      (derivedSupportedPushforward X T hT)
      (derivedRestrictPush X (openComplement T hT))
      (derivedSupportedPushforwardUnit X T hT)
      (derivedRestrictPushUnit X (openComplement T hT)) A)).1
    (isZero_derivedRestrictPush_of_supported X T hT A hA)

end Vanishing

section Quasicoherence

variable (X : Scheme.{u}) (U : X.Opens)

/-- Restriction of modules to an open subspace is the pullback of modules along the inclusion:
both are left adjoint to the direct image, which for an open subspace is the same functor in
either spelling. -/
def jStarIsoModulePullback :
    jStar U (structureSheafRing X.toRingedSpace) ≅
      modulePullback (X.toRingedSpace.ofRestrict U.isOpenEmbedding) :=
  (jStarAdjunction U (structureSheafRing X.toRingedSpace)).leftAdjointUniq
    (modulePullbackPushforwardAdjunction (X.toRingedSpace.ofRestrict U.isOpenEmbedding))

/-- Restriction to an open subspace preserves quasi-coherence, being the pullback of modules
along the inclusion. -/
theorem isQuasicoherent_jStar_obj (M : X.Modules) (hM : M.IsQuasicoherent) :
    ((jStar U (structureSheafRing X.toRingedSpace)).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((jStarIsoModulePullback X U).app M).symm
    (@SheafOfModules.modulePullback_isQuasicoherent _ _
      (X.toRingedSpace.ofRestrict U.isOpenEmbedding) M hM)

/-- Restriction to an open subspace preserves quasi-coherent cohomology: it is exact, so its
effect on the derived category commutes with the cohomology functors. -/
theorem derivedQuasiCoherent_jStar_mapDerivedCategory
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)
      ((jStar U (structureSheafRing X.toRingedSpace)).mapDerivedCategory.obj E) := by
  intro n
  have hn : ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing X.toRingedSpace)) n).obj E).IsQuasicoherent := hE n
  have hiso :=
    (exactFunctorDerivedHomologyIso (jStar U (structureSheafRing X.toRingedSpace)) n).app E
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso hiso.symm
    (isQuasicoherent_jStar_obj X U _ hn)

/-- Retrocompactness of an open subset is quasi-compactness of its inclusion. -/
@[ega "0 9.1.1" "partial", sga "3 VIA 2.6.3" "partial", sga "3 VIB 3.7" "partial"]
theorem quasiCompact_ι_of_isRetrocompact (hU : IsRetrocompact (U : Set X)) :
    QuasiCompact U.ι :=
  quasiCompact_iff_isSpectralMap.mpr (by
    show IsSpectralMap (Subtype.val : U → X)
    exact IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hU)

/-- **Stacks 08D5 for the inclusion of a retrocompact open.** `Rj_*(E|_U)` has quasi-coherent
cohomology whenever `E` does. This is the only place retrocompactness of `U` is used: it is
exactly quasi-compactness of `j`, which together with the automatic quasi-separatedness of an
open immersion is the hypothesis of Stacks 08D5. -/
theorem derivedQuasiCoherent_derivedRestrictPush (hU : IsRetrocompact (U : Set X))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((derivedRestrictPush X.toRingedSpace U).obj E) :=
  let : QuasiCompact U.ι := quasiCompact_ι_of_isRetrocompact X U hU
  let : QuasiSeparated U.ι := inferInstance
  AlgebraicGeometry.isQuasicoherent_derivedPushforward U.ι
    ⟨(jStar U (structureSheafRing X.toRingedSpace)).mapDerivedCategory.obj E,
      derivedQuasiCoherent_jStar_mapDerivedCategory X U E hE⟩

end Quasicoherence

section Main

variable (X : Scheme.{u}) (T : Set X) (hT : IsClosed T)

/-- Quasi-coherent cohomology is a triangulated subcategory of `D(𝒪_X)`: quasi-coherent
modules are a weak Serre subcategory (Stacks 06VT), so Stacks 06UP applies. -/
instance derivedQuasiCoherent_isTriangulated :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)

/-- Quasi-coherent cohomology is a strictly full subcategory of `D(𝒪_X)`. -/
instance derivedQuasiCoherent_isClosedUnderIsomorphisms :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)

/-- **The quasi-coherence half of Stacks 0G7G (1).** For `E` in `D_QCoh(𝒪_X)` the complex
`i_* R𝓗_T(E)` again has quasi-coherent cohomology.

This is the content of the source's proof: the triangle of Stacks 0G72,
`i_* R𝓗_T(E) ⟶ E ⟶ Rj_*(E|_U) ⟶ (i_* R𝓗_T(E))⟦1⟧`, has its second and third terms in
`D_QCoh(𝒪_X)` — the second by hypothesis and the third by Stacks 08D5, which is where
retrocompactness of `U = X ∖ T` is used — and `D_QCoh(𝒪_X)` is a triangulated subcategory, so
the first term is in it too. -/
theorem derivedQuasiCoherent_derivedSupportedPushforward (hTc : IsRetrocompact Tᶜ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((derivedSupportedPushforward X.toRingedSpace T hT).obj E) :=
  let := derivedQuasiCoherent_isTriangulated X
  let := derivedQuasiCoherent_isClosedUnderIsomorphisms X
  ObjectProperty.ext_of_isTriangulatedClosed₁
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)) _
    (derivedSupportedSectionsTriangle_distinguished X.toRingedSpace T hT
      (derivedSupportedPushforward X.toRingedSpace T hT)
      (derivedRestrictPush X.toRingedSpace (openComplement T hT))
      (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
      (derivedRestrictPushUnit X.toRingedSpace (openComplement T hT)) E) hE
    (derivedQuasiCoherent_derivedRestrictPush X (openComplement T hT) hTc E hE)

/-- **The support half of Stacks 0G7G (1).** Every cohomology sheaf of `i_* R𝓗_T(E)` has
vanishing stalks off `T`, because the complex is a direct image from `T`. This is Stacks 0AEF
(1) and needs neither quasi-coherence of `E` nor retrocompactness of `X ∖ T`. -/
theorem cohomologySupportedOn_derivedSupportedPushforward
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      ((derivedSupportedPushforward X.toRingedSpace T hT).obj E) :=
  pushforward_supported X.toRingedSpace T hT
    ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj E)

/-- **Stacks 0G7G (1).** Let `X` be a scheme, let `T ⊆ X` be a closed subset whose open
complement `X ∖ T` is retrocompact, and let `i : T → X` be the inclusion. For `E` in
`D_QCoh(𝒪_X)` the complex `i_* R𝓗_T(E)` lies in `D_{QCoh, T}(𝒪_X)`: its cohomology sheaves
are quasi-coherent and supported on `T`. -/
@[stacks 0G7G "part (1)"]
theorem quasiCoherentSupported_derivedSupportedPushforward (hTc : IsRetrocompact Tᶜ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    Stacks.Duality.quasiCoherentSupported X T
      ((derivedSupportedPushforward X.toRingedSpace T hT).obj E) :=
  ⟨derivedQuasiCoherent_derivedSupportedPushforward X T hT hTc E hE,
    cohomologySupportedOn_derivedSupportedPushforward X T hT E⟩

/-! ### Part (2): the adjunction -/

/-- The inclusion functor `D_{QCoh,T}(𝒪_X) ⥤ D_QCoh(𝒪_X)`. -/
def quasiCoherentSupportedInclusion :
    (Stacks.Duality.quasiCoherentSupported X T).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).lift
    (Stacks.Duality.quasiCoherentSupported X T).ι fun A => A.property.1

/-- The functor `i_* ∘ R𝓗_T : D_QCoh(𝒪_X) ⥤ D_{QCoh,T}(𝒪_X)`, which is `i_* R𝓗_T`
corestricted to `D_{QCoh,T}(𝒪_X)` using part (1). -/
def quasiCoherentDerivedSupport (hTc : IsRetrocompact Tᶜ) :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ⥤
      (Stacks.Duality.quasiCoherentSupported X T).FullSubcategory :=
  (Stacks.Duality.quasiCoherentSupported X T).lift
    ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
      derivedSupportedPushforward X.toRingedSpace T hT)
    fun E => quasiCoherentSupported_derivedSupportedPushforward X T hT hTc E.obj E.property

/-- On `D_{QCoh,T}(𝒪_X)` the canonical map `i_* R𝓗_T(A) ⟶ A` is a natural isomorphism: every
complex supported on `T` is recovered from its derived supported sections. -/
def supportedCounitIso :
    (Stacks.Duality.quasiCoherentSupported X T).ι ⋙
        derivedSupportedPushforward X.toRingedSpace T hT ≅
      (Stacks.Duality.quasiCoherentSupported X T).ι :=
  haveI : ∀ A : (Stacks.Duality.quasiCoherentSupported X T).FullSubcategory,
      IsIso ((Functor.whiskerLeft (Stacks.Duality.quasiCoherentSupported X T).ι
        (derivedSupportedSectionsToId X.toRingedSpace T
          (derivedSupportedPushforward X.toRingedSpace T hT)
          (derivedSupportedPushforwardUnit X.toRingedSpace T hT))).app A) := fun A =>
    isIso_derivedSupportedSectionsToId_app_of_supported X.toRingedSpace T hT A.obj A.property.2
  haveI : IsIso (Functor.whiskerLeft (Stacks.Duality.quasiCoherentSupported X T).ι
      (derivedSupportedSectionsToId X.toRingedSpace T
        (derivedSupportedPushforward X.toRingedSpace T hT)
        (derivedSupportedPushforwardUnit X.toRingedSpace T hT))) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (Stacks.Duality.quasiCoherentSupported X T).ι
    (derivedSupportedSectionsToId X.toRingedSpace T
      (derivedSupportedPushforward X.toRingedSpace T hT)
      (derivedSupportedPushforwardUnit X.toRingedSpace T hT))) ≪≫
    (Stacks.Duality.quasiCoherentSupported X T).ι.rightUnitor

/-- **Stacks 0G7G (2).** Let `X` be a scheme, let `T ⊆ X` be a closed subset whose open
complement is retrocompact, and let `i : T → X` be the inclusion. The functor
`i_* ∘ R𝓗_T : D_QCoh(𝒪_X) ⥤ D_{QCoh,T}(𝒪_X)` is right adjoint to the inclusion functor
`D_{QCoh,T}(𝒪_X) ⥤ D_QCoh(𝒪_X)`.

The adjunction is the restriction of the ambient adjunction `i_* ⊣ R𝓗_T` of Stacks 0A3B along
the two fully faithful inclusions: on the left `R𝓗_T` identifies `D_{QCoh,T}(𝒪_X)` with a full
subcategory of `D(𝒪_X|_T)`, because the counit `i_* R𝓗_T(A) ⟶ A` is invertible there, and on
the right `D_QCoh(𝒪_X)` is a full subcategory of `D(𝒪_X)`. -/
@[stacks 0G7G "part (2)"]
def quasiCoherentSupportedInclusionAdj (hTc : IsRetrocompact Tᶜ) :
    quasiCoherentSupportedInclusion X T ⊣ quasiCoherentDerivedSupport X T hT hTc :=
  letI := pushforward_preservesFiniteLimits X.toRingedSpace T
  letI := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  let P := Stacks.Duality.quasiCoherentSupported X T
  let Qp := DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
  let hInc : ∀ A : P.FullSubcategory, Qp (P.ι.obj A) := fun A => A.property.1
  let F : Qp.FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    Qp.ι ⋙ derivedSupportedPushforward X.toRingedSpace T hT
  let hG : ∀ E : Qp.FullSubcategory, P (F.obj E) := fun E =>
    quasiCoherentSupported_derivedSupportedPushforward X T hT hTc E.obj E.property
  let L' := (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory
  let RH := derivedSupportedSectionsOnClosed X.toRingedSpace T hT
  let iC := P.ι ⋙ RH
  let comm1 : iC ⋙ L' ≅ Qp.lift P.ι hInc ⋙ Qp.ι :=
    supportedCounitIso X T hT ≪≫ (Qp.liftCompιIso P.ι hInc).symm
  let comm2 : Qp.ι ⋙ RH ≅ P.lift F hG ⋙ iC :=
    Functor.isoWhiskerLeft (Qp.ι ⋙ RH)
        (asIso (derivedPushforwardAdjunction X.toRingedSpace T hT).unit) ≪≫
      (Functor.isoWhiskerRight (P.liftCompιIso F hG) RH).symm
  haveI hLff : L'.FullyFaithful :=
    (derivedPushforwardAdjunction X.toRingedSpace T hT).fullyFaithfulLOfIsIsoUnit
  haveI := hLff.full
  haveI := hLff.faithful
  haveI : (Qp.lift P.ι hInc ⋙ Qp.ι).Full :=
    Functor.Full.of_iso (F := P.ι) (Qp.liftCompιIso P.ι hInc).symm
  haveI : (Qp.lift P.ι hInc ⋙ Qp.ι).Faithful :=
    Functor.Faithful.of_iso (F := P.ι) (Qp.liftCompιIso P.ι hInc).symm
  haveI : (iC ⋙ L').Full := Functor.Full.of_iso (F := Qp.lift P.ι hInc ⋙ Qp.ι) comm1.symm
  haveI : (iC ⋙ L').Faithful :=
    Functor.Faithful.of_iso (F := Qp.lift P.ι hInc ⋙ Qp.ι) comm1.symm
  haveI : iC.Full := Functor.Full.of_comp_faithful iC L'
  haveI : iC.Faithful := Functor.Faithful.of_comp iC L'
  (derivedPushforwardAdjunction X.toRingedSpace T hT).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful iC) Qp.fullyFaithfulι comm1 comm2

end Main

end Stacks.Perfect.SupportedQuasicoherent

end
