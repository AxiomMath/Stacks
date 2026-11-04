module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedCounitForget
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsForgetPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HomotopyCategory

/-!
# The units of the two readings of Stacks 0G74 part (2), factor by factor

Both readings of [Stacks, Tag 0G74] part (2) — the one stated on the closed subset `T`
(`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison`) and the one with
`i_*` folded in (`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`)
— are `CategoryTheory.Functor.rightDerivedDesc` of a transported underived comparison.  Comparing
them means comparing those transported comparisons, which are seven-factor composites of
whiskerings and associators, and the derivation units they are descended along, which are
three-factor composites.

This file opens all of them up at an object of the homotopy category.

## Main results

* `forgetfulSupportedEndoUnit_app` and `localCohomologySheafForgetComparison_fac_app`: the
  derivation unit of `RH ⋙ Φ` and the characterising factorization of the comparison on `T`, at
  an object.
* `derivedSupportedPushforwardUnit_app`, `derivedSupportedPushforwardSplit_hom_app` and
  `derivedAbelianSupportedPushforwardSplit_hom_app`: the derivation unit of `i_* R𝓗_T` and the
  two reassociations that split the exact direct image off, at an object.  Of the four factors of
  each reassociation two are associators and contribute an identity; what survives is the
  localization of the comparison of [Stacks, Tag 0G6N] and the inverse of
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the direct image.
* `supportedSheafForgetUnit_app` and `abelianSupportedEndoForgetUnit_app`: **the two seven-factor
  units at an object**.  Three of the seven factors — two associators and the comparison of
  homotopy categories attached to an identity isomorphism — contribute an identity, and the two
  units become four-factor composites of the same shape, differing only in which comparison of
  homotopy categories of the underived forgetful isomorphism occurs and in which derived functor
  the last factor is read in.

## Implementation notes

**Why everything is `simp only` followed by an `exact`.**  The identities contributed by the
associators and by `CategoryTheory.Functor.mapHomotopyCategoryCompIso` of an identity isomorphism
are identities of objects with two definitionally equal but syntactically different spellings, so
`simp` will not cancel them: the rewrite it would have to perform is type-correct only at default
transparency.  Each cancellation is therefore done by a lemma stated at a variable category —
`unit_collapse`, `id_sandwich`, `comp_assoc_id` — and applied with `exact`.  This is the device
of `Stacks.Perfect.AbelianCechDerivedSquare.square_formal`.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.ModulePushforwardComparison
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.UnderlyingAbelianSheaf (underlyingDerivedSheaf)
open Stacks.Perfect.SupportedQuasicoherent
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Perfect.SupportedEndoForget

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (T : Set X.carrier) (hT : IsClosed T)

private lemma unit_collapse {C₀ : Type*} [Category* C₀] {A B B' D E : C₀}
    (f1 : A ⟶ B) (f3 : B ⟶ B') (g : B' ⟶ B') (hg : g = 𝟙 B') (f6 : B' ⟶ D) (f7 : D ⟶ E) :
    f1 ≫ 𝟙 B ≫ f3 ≫ g ≫ 𝟙 B' ≫ f6 ≫ f7 = f1 ≫ f3 ≫ f6 ≫ f7 := by
  rw [hg]; simp

private lemma id_sandwich {C₀ : Type*} [Category* C₀] {A B M : C₀} (a : A ⟶ B) (b : B ⟶ M) :
    a ≫ 𝟙 B ≫ b ≫ 𝟙 M = a ≫ b := by simp

/-- In any category, `a ≫ b ≫ 𝟙 M = a ≫ b`. -/
lemma comp_assoc_id {C₀ : Type*} [Category* C₀] {A B M : C₀} (a : A ⟶ B) (b : B ⟶ M) :
    a ≫ b ≫ 𝟙 M = a ≫ b := by rw [Category.comp_id]

section Units

variable (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
  (aH : (supportedSectionsFunctor X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)

/-- At an object `K` of the homotopy category, the derivation unit
`forgetfulSupportedEndoUnit X T RH aH` is the image of `aH.app K` under the functor to the derived
category of underlying abelian sheaves. -/
theorem forgetfulSupportedEndoUnit_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    (forgetfulSupportedEndoUnit X T RH aH).app K =
      (underlyingDerivedSheaf (structureSheafRing X)).map (aH.app K) := by
  simp [forgetfulSupportedEndoUnit]

end Units

/-- At an object `K` of the homotopy category, the derivation unit
`derivedSupportedPushforwardUnit X T hT` is the component of
`derivedSupportedPushforwardSplit X T hT` followed by the derived direct image along the closed
inclusion of the component of `derivedSupportedSectionsOnClosedUnit X T hT`. -/
theorem derivedSupportedPushforwardUnit_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    (derivedSupportedPushforwardUnit X T hT).app K =
      (derivedSupportedPushforwardSplit X T hT).hom.app K ≫
        (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory.map
          ((derivedSupportedSectionsOnClosedUnit X T hT).app K) := by
  simp only [derivedSupportedPushforwardUnit]
  exact comp_assoc_id _ _

section Sheaf

variable
  (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}))
  (aHab : (abelianSupportedSectionsOnClosed X T hT).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
  (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X T))))
  (aH : (supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)

/-- At an object `K` of the homotopy category, the image of `aH.app K` in the derived category of
underlying abelian sheaves, followed by the component of
`localCohomologySheafForgetComparison X T hT RHab aHab RH aH` at `K`, is the component of
`supportedSheafForgetUnit X T hT RHab aHab` at `K`. -/
theorem localCohomologySheafForgetComparison_fac_app
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))]
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    (underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X T))).map
          (aH.app K) ≫
        (localCohomologySheafForgetComparison X T hT RHab aHab RH aH).app
          (DerivedCategory.Qh.obj K) =
      (supportedSheafForgetUnit X T hT RHab aHab).app K := by
  have h := congr_app (localCohomologySheafForgetComparison_fac X T hT RHab aHab RH aH) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, forgetfulSupportedSheafUnit,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id] at h
  exact h

end Sheaf

/-- At an object `K` of the homotopy category, the component of
`derivedSupportedPushforwardSplit X T hT` is the localization of the inverse comparison of
homotopy categories attached to `supportedSectionsOnClosedFunctor_comp_modulePushforward_iso`,
followed by the inverse of `mapDerivedCategoryFactorsh` of the direct image. -/
theorem derivedSupportedPushforwardSplit_hom_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    (derivedSupportedPushforwardSplit X T hT).hom.app K =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
            (ComplexShape.up ℤ)).inv.app K) ≫
        (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.inv.app
          (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) := by
  simp only [derivedSupportedPushforwardSplit, Iso.trans_hom, NatTrans.comp_app]
  exact id_sandwich _ _

/-- At an object `L` of the homotopy category of abelian sheaves, the component of
`derivedAbelianSupportedPushforwardSplit X T hT` is the localization of the inverse comparison of
homotopy categories attached to `abelianSupportedSectionsRealizedCompPushforwardIso`, followed by
the inverse of `mapDerivedCategoryFactorsh` of the abelian direct image. -/
theorem derivedAbelianSupportedPushforwardSplit_hom_app
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)) :
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    (derivedAbelianSupportedPushforwardSplit X T hT).hom.app L =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (abelianSupportedSectionsRealizedCompPushforwardIso T hT)
            (ComplexShape.up ℤ)).inv.app L) ≫
        (abelianClosedPushforward T).mapDerivedCategoryFactorsh.inv.app
          (((abelianSupportedSectionsOnClosed X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj L) := by
  simp only [derivedAbelianSupportedPushforwardSplit, Iso.trans_hom, NatTrans.comp_app]
  exact id_sandwich _ _

open Stacks.Cohomology.SupportedSectionsForgetPushforward
  Stacks.Cohomology.AbelianSupportedCounitForget in
/-- At an object `K` of the homotopy category, the component of
`supportedSheafForgetUnit X T hT RHab aHab` is the four-factor composite of
`mapDerivedCategoryFactorsh` of the forgetful functor on `T`, the localization of
`forgetCompIsoOnClosed X T hT`, `aHab` at the underlying complex of abelian sheaves, and `RHab`
applied to the inverse of `mapDerivedCategoryFactorsh` of the forgetful functor on `X`. -/
theorem supportedSheafForgetUnit_app
    (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}))
    (aHab : (abelianSupportedSectionsOnClosed X T hT).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    (supportedSheafForgetUnit X T hT RHab aHab).app K =
      (_root_.SheafOfModules.toSheaf
            (structureSheafRing (closedSubsetRingedSpace X T))).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((forgetCompIsoOnClosed X T hT).hom.app K) ≫
        aHab.app (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
        RHab.map ((_root_.SheafOfModules.toSheaf
          (structureSheafRing X)).mapDerivedCategoryFactorsh.inv.app K) := by
  simp only [supportedSheafForgetUnit, NatTrans.comp_app]
  refine unit_collapse _ _ _ ?_ _ _
  exact Eq.trans (congrArg DerivedCategory.Qh.map
    (show (@Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
      (Iso.refl (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        abelianSupportedSectionsOnClosed X T hT))
      (by exact inferInstanceAs (_root_.SheafOfModules.toSheaf (structureSheafRing X)).Additive)
      (by exact abelianSupportedSectionsOnClosed_additive X T hT)
      (by exact forget_abelianSupportedSectionsOnClosed_additive X T hT)
      (ComplexShape.up ℤ)).inv.app K = 𝟙 _ from rfl)) (DerivedCategory.Qh.map_id _)

open Stacks.Cohomology.SupportedSectionsForgetPushforward
  Stacks.Cohomology.AbelianSupportedCounitForget in
/-- At an object `K` of the homotopy category, the component of
`abelianSupportedEndoForgetUnit X T RHab aHab` is the four-factor composite of
`mapDerivedCategoryFactorsh` of the forgetful functor on `X`, the localization of
`forgetCompIso X T`, `aHab` at the underlying complex of abelian sheaves, and `RHab` applied to the
inverse of `mapDerivedCategoryFactorsh` of the forgetful functor on `X`. -/
theorem abelianSupportedEndoForgetUnit_app
    (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))
    (aHab : (abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    (abelianSupportedEndoForgetUnit X T RHab aHab).app K =
      (_root_.SheafOfModules.toSheaf
            (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsFunctor X T).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((forgetCompIso X T).hom.app K) ≫
        aHab.app (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
        RHab.map ((_root_.SheafOfModules.toSheaf
          (structureSheafRing X)).mapDerivedCategoryFactorsh.inv.app K) := by
  simp only [abelianSupportedEndoForgetUnit, NatTrans.comp_app]
  refine unit_collapse _ _ _ ?_ _ _
  exact Eq.trans (congrArg DerivedCategory.Qh.map
    (show (@Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
      (Iso.refl (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        abelianSupportedSections T))
      (by exact inferInstanceAs (_root_.SheafOfModules.toSheaf (structureSheafRing X)).Additive)
      (by exact abelianSupportedSections_additive T)
      (by exact forget_abelianSupportedSections_additive X T)
      (ComplexShape.up ℤ)).inv.app K = 𝟙 _ from rfl)) (DerivedCategory.Qh.map_id _)

end Stacks.Perfect.SupportedEndoForget

end
