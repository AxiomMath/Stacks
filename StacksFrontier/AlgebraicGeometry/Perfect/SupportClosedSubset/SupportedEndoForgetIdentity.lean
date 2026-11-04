module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechDerivedSquare
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetSplit

/-!
# The two readings of Stacks 0G74 part (2) agree

[Stacks, Tag 0G74] part (2) is stated twice in the library: on the closed subset `T`, as
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison`, and with the direct
image `i_*` folded in, as
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`.  This file proves
that the second is the first, read through the comparison
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` that moves
the direct image past the forgetful functor on derived categories:

`RH_T ⋆ cmp ≫ (0G74 on T) ⋆ i_*^{ab,D} = (0G74 with i_* folded in)`.

Both sides are `CategoryTheory.Functor.rightDerivedDesc` of the same ambient derived functor
`i_* R𝓗_T ⋙ Φ_X^D` at the same derivation unit, so
`CategoryTheory.Functor.rightDerived_ext` reduces the equality to one identity between the two
transported units, which is what the bulk of the file establishes.

## Main results

* `endoForgetComparison_eq`: the equality of the two readings, for a closed subset of a ringed
  space, at the canonical derived functors.
* `forgetComparison_eq`: the same at the ringed space of a scheme, with the right-hand side
  written as `Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison`.
* `unitIdentity` and `unitIdentity_normalized`: the identity of the two transported units at an
  object of the homotopy category, and its normalized form.

## Implementation notes

**Why the unit identity is split across two declarations.**  `unitIdentity` opens the two
seven-factor units up with four rewrites and one `simp only`, and `unitIdentity_normalized`
applies `Stacks.Perfect.SupportedEndoForgetSplit.unitIdentity_formal` to its five inputs.  Doing
both in one declaration exhausts the default heartbeat limit — the last of the five hypotheses,
which matches the goal syntactically, is then rejected for want of budget.  No `set_option` is
used anywhere in this development.

**Why `apply` and not `exact`.**  `unitIdentity_formal` is applied with `apply`, so that its
conclusion is unified with the goal before any hypothesis is elaborated, and the five hypotheses
are discharged as named goals.  The order matters: `hM` must come before `hnat2`, because the
morphism `t₂` common to both is pinned down by `hM` and appears in `hnat2` only.

**No `@[stacks ...]` attribute is attached to any declaration here**, and nothing here proves
[Stacks, Tag 0G74] or [Stacks, Tag 0G85].

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.ModulePushforwardComparison
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.SupportedSectionsForgetPushforward
open Stacks.Cohomology.AbelianSupportedCounitForget (forgetCompIso)
open Stacks.Cohomology.UnderlyingAbelianSheaf (underlyingDerivedSheaf)
open Stacks.Perfect.SupportedEndoForget
open Stacks.Perfect.SupportedEndoForgetSplit
open Stacks.Perfect.SupportedQuasicoherent
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Perfect.SupportedEndoForgetIdentity

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (T : Set X.carrier) (hT : IsClosed T)

/-- **The unit identity, at the normalized form of both sides.** At an object `K` of the homotopy
category, the two transported units, each written out as a composite of its factors, agree. -/
theorem unitIdentity_normalized
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    letI : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
      abelianClosedPushforward_preservesFiniteColimits X T hT
    (underlyingDerivedSheaf (structureSheafRing X)).map
          (DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso
              (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
              (ComplexShape.up ℤ)).inv.app K)) ≫
        (underlyingDerivedSheaf (structureSheafRing X)).map
            ((modulePushforward (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.inv.app
              (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K)) ≫
          (derivedModulePushforwardCompToSheafIso (closedSubsetInclusion X T)).hom.app
              (DerivedCategory.Qh.obj
                (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj K)) ≫
            (abelianClosedPushforward T).mapDerivedCategory.map
              ((_root_.SheafOfModules.toSheaf
                    (structureSheafRing
                      (closedSubsetRingedSpace X T))).mapDerivedCategoryFactorsh.hom.app
                  (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
                    (ComplexShape.up ℤ)).obj K) ≫
                DerivedCategory.Qh.map ((forgetCompIsoOnClosed X T hT).hom.app K) ≫
                  (derivedAbelianSupportedSectionsOnClosedUnit X T hT).app
                      (((_root_.SheafOfModules.toSheaf
                        (structureSheafRing X)).mapHomotopyCategory
                        (ComplexShape.up ℤ)).obj K) ≫
                    (derivedAbelianSupportedSectionsOnClosed X T hT).map
                      ((_root_.SheafOfModules.toSheaf
                        (structureSheafRing X)).mapDerivedCategoryFactorsh.inv.app K)) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app
            (((supportedSectionsFunctor X T).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((forgetCompIso X T).hom.app K) ≫
            (DerivedCategory.Qh.map
                  ((Functor.mapHomotopyCategoryCompIso
                    (abelianSupportedSectionsRealizedCompPushforwardIso T hT)
                    (ComplexShape.up ℤ)).inv.app
                    (((_root_.SheafOfModules.toSheaf
                      (structureSheafRing X)).mapHomotopyCategory
                      (ComplexShape.up ℤ)).obj K)) ≫
                (abelianClosedPushforward T).mapDerivedCategoryFactorsh.inv.app
                    (((_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
                      abelianSupportedSectionsOnClosed X T hT).mapHomotopyCategory
                      (ComplexShape.up ℤ)).obj K) ≫
                  (abelianClosedPushforward T).mapDerivedCategory.map
                    ((derivedAbelianSupportedSectionsOnClosedUnit X T hT).app
                      (((_root_.SheafOfModules.toSheaf
                        (structureSheafRing X)).mapHomotopyCategory
                        (ComplexShape.up ℤ)).obj K))) ≫
            (derivedAbelianSupportedPushforward X T hT).map
              ((_root_.SheafOfModules.toSheaf
                (structureSheafRing X)).mapDerivedCategoryFactorsh.inv.app K) := by
  apply unitIdentity_formal
  case hB =>
    exact fach_comp X T hT
      (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  case hnat1 => exact factorsh_naturality_forget X T hT K
  case hM => exact Qh_forgetPushforwardSquare X T hT K
  case hnat2 => exact factorsh_naturality_closedPushforward X T hT K
  case hR7 => rfl

/-- **The right-hand side of the unit identity, with the exact direct image split off.**  The
seven-factor unit `abelianSupportedEndoForgetUnit` at the canonical abelian derived functor is the
normalized form that `unitIdentity_normalized` compares with the left-hand side. -/
theorem unitIdentity
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    letI : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
      abelianClosedPushforward_preservesFiniteColimits X T hT
    (underlyingDerivedSheaf (structureSheafRing X)).map
          ((derivedSupportedPushforwardSplit X T hT).hom.app K) ≫
        (derivedModulePushforwardCompToSheafIso (closedSubsetInclusion X T)).hom.app
          (DerivedCategory.Qh.obj (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
        (abelianClosedPushforward T).mapDerivedCategory.map
          ((supportedSheafForgetUnit X T hT
            (derivedAbelianSupportedSectionsOnClosed X T hT)
            (derivedAbelianSupportedSectionsOnClosedUnit X T hT)).app K) =
      (abelianSupportedEndoForgetUnit X T (derivedAbelianSupportedPushforward X T hT)
        (derivedAbelianSupportedPushforwardUnit X T hT)).app K := by
  let := pushforward_preservesFiniteLimits X T
  let := pushforward_preservesFiniteColimits X T hT
  let := abelianClosedPushforward_preservesFiniteLimits X T hT
  let := abelianClosedPushforward_preservesFiniteColimits X T hT
  let : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
    abelianClosedPushforward_preservesFiniteColimits X T hT
  rw [derivedSupportedPushforwardSplit_hom_app, supportedSheafForgetUnit_app,
    abelianSupportedEndoForgetUnit_app, derivedAbelianSupportedPushforwardUnit_app_forget]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  exact unitIdentity_normalized X T hT K

/-- For a closed subset `T` of a ringed space `X`, the comparison
`abelianSupportedEndoForgetComparison` at the canonical derived functors equals
`localCohomologySheafForgetComparison` whiskered by the derived direct image
`(abelianClosedPushforward T).mapDerivedCategory`, precomposed with the comparison
`derivedModulePushforwardCompToSheafIso` moving the direct image past the forgetful functor. -/
theorem endoForgetComparison_eq :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    letI : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
      abelianClosedPushforward_preservesFiniteColimits X T hT
    Functor.whiskerLeft (derivedSupportedSectionsOnClosed X T hT)
          (derivedModulePushforwardCompToSheafIso (closedSubsetInclusion X T)).hom ≫
        Functor.whiskerRight
          (localCohomologySheafForgetComparison X T hT
            (derivedAbelianSupportedSectionsOnClosed X T hT)
            (derivedAbelianSupportedSectionsOnClosedUnit X T hT)
            (derivedSupportedSectionsOnClosed X T hT)
            (derivedSupportedSectionsOnClosedUnit X T hT))
          (abelianClosedPushforward T).mapDerivedCategory =
      abelianSupportedEndoForgetComparison X T
        (derivedAbelianSupportedPushforward X T hT)
        (derivedAbelianSupportedPushforwardUnit X T hT)
        (derivedSupportedPushforward X T hT)
        (derivedSupportedPushforwardUnit X T hT) := by
  refine Functor.rightDerived_ext
    (derivedSupportedPushforward X T hT ⋙ underlyingDerivedSheaf (structureSheafRing X))
    (forgetfulSupportedEndoUnit X T (derivedSupportedPushforward X T hT)
      (derivedSupportedPushforwardUnit X T hT))
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))
    (underlyingDerivedSheaf (structureSheafRing X) ⋙ derivedAbelianSupportedPushforward X T hT)
    _ _ ?_
  rw [abelianSupportedEndoForgetComparison_fac]
  ext K
  simp only [NatTrans.comp_app]
  exact (unitComp_eq X T hT K).trans (unitIdentity X T hT K)

/-- **[Stacks, Tag 0G74] part (2) with `i_*` folded in is the comparison on `T`, read through the
derived pushforward/forget comparison** — `endoForgetComparison_eq` at the ringed space of a
scheme, with the right-hand side written as
`Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison`. -/
theorem forgetComparison_eq {Y : Scheme.{u}} {S : Set Y} (hS : IsClosed S) :
    letI := pushforward_preservesFiniteLimits Y.toRingedSpace S
    letI := pushforward_preservesFiniteColimits Y.toRingedSpace S hS
    letI := abelianClosedPushforward_preservesFiniteLimits Y.toRingedSpace S hS
    letI := abelianClosedPushforward_preservesFiniteColimits Y.toRingedSpace S hS
    letI : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion Y.toRingedSpace S)) :=
      abelianClosedPushforward_preservesFiniteColimits Y.toRingedSpace S hS
    Functor.whiskerLeft (derivedSupportedSectionsOnClosed Y.toRingedSpace S hS)
          (derivedModulePushforwardCompToSheafIso
            (closedSubsetInclusion Y.toRingedSpace S)).hom ≫
        Functor.whiskerRight
          (localCohomologySheafForgetComparison Y.toRingedSpace S hS
            (derivedAbelianSupportedSectionsOnClosed Y.toRingedSpace S hS)
            (derivedAbelianSupportedSectionsOnClosedUnit Y.toRingedSpace S hS)
            (derivedSupportedSectionsOnClosed Y.toRingedSpace S hS)
            (derivedSupportedSectionsOnClosedUnit Y.toRingedSpace S hS))
          (abelianClosedPushforward S).mapDerivedCategory =
      Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison hS :=
  endoForgetComparison_eq Y.toRingedSpace S hS

end Stacks.Perfect.SupportedEndoForgetIdentity

end
