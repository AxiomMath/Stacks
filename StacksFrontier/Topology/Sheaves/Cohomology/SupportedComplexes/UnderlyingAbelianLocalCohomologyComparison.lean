module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologySheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianSectionsWithSupport
import StacksCore.Tactic.StacksAttribute

/-!
# The derived local cohomology sheaves and the underlying abelian sheaf

Let `Z` be a closed subset of a ringed space `X`, let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the
inclusion and let `K` be an object of the unbounded derived category `D(𝒪_X)` with image `K_ab`
in `D(ℤ_X)`. Writing `RH_Z` for a right derived functor of sections supported on `Z` — of
`𝒪_X`-modules on one side, of abelian sheaves on the other — this file constructs the canonical
comparison

`RH_Z(K)_ab ⟶ RH_Z(K_ab)`

in `D(Ab(Z))`, natural in `K`. This is the map of Stacks 0G74 part (2). Its invertibility is
proved in `UnderlyingAbelianLocalCohomologyInvertible.lean`; see the implementation notes.

## Main definitions

* `abelianSupportedSectionsOnClosed`: the functor `H_Z : Ab(X) ⥤ Ab(Z)` of
  `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor`, with source and target spelled as
  sheaves for the Grothendieck topology of opens.
* `supportedSheafForgetUnit`: the comparison on homotopy categories, built from the underived
  comparison `supportedSectionsOnClosedForgetIso` and the derivation unit of a right derived
  functor of abelian supported sections.
* `localCohomologySheafForgetComparison` (Stacks 0G74, part (2), the canonical map):
  `RH_Z(K)_ab ⟶ RH_Z(K_ab)`.

## Main results

* `localCohomologySheafForgetComparison_fac`: the comparison is the unique transformation
  compatible with `supportedSheafForgetUnit`, so it does not depend on a choice of resolutions.
* `isIso_localCohomologySheafForgetComparison`: the comparison is invertible as soon as the
  transported unit `supportedSheafForgetUnit` exhibits `K ↦ RH_Z(K_ab)` as a right derived
  functor of module-level supported sections. That hypothesis holds, so the comparison is in
  fact always invertible; this is
  `isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor` in
  `UnderlyingAbelianLocalCohomologyInvertible.lean`.
* `exists_rightDerivedFunctor_supportedSectionsOnClosed`: both derived functors quantified over
  exist, so the statement is not about an empty family.

## Implementation notes

As in Tag 0G71 and in part (1) of this tag
(`Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.sectionsWithSupportForgetComparison`)
the two derived functors are quantified over rather than fixed: the comparison is constructed
for arbitrary functors on the unbounded derived category equipped with
`CategoryTheory.Functor.IsRightDerivedFunctor` data, and
`exists_rightDerivedFunctor_supportedSectionsOnClosed` records that such data exists on both
sides.

The construction is the universal property of the right derived functor. Forgetting the module
structure is exact, so it carries a right derived functor of `H_Z` to one again; that is
`isRightDerivedFunctor_forgetfulSupportedSheafUnit`, proved by checking invertibility of the
transported unit on K-injective complexes. Descending `supportedSheafForgetUnit` along that
right derived functor gives the comparison.

`abelianSupportedSectionsOnClosed` repeats
`ClosedImmersionSheaves.supportedSectionsOnClosedFunctor` with its source and target spelled as
`CategoryTheory.Sheaf (Opens.grothendieckTopology _) AddCommGrpCat` rather than through
`TopCat.Sheaf`. The two spellings are definitionally equal but `TopCat.Sheaf` is a `def` with a
derived `Category` instance, so the `Preadditive` structures of the one are not found by
instance search for the other, and the degreewise and homotopy-category constructions —
all of which need an additive functor — do not elaborate in the mixed spelling. Everything in
this file is therefore stated in the `Sheaf` spelling, and
`abelianSupportedSectionsOnClosedForgetIso` is `supportedSectionsOnClosedForgetIso` read in it.

**Where invertibility is proved.** Invertibility of the comparison, the substance of Stacks
0G74 part (2), is not proved in this file. By `isIso_localCohomologySheafForgetComparison` what
it comes down to is that `supportedSheafForgetUnit` is a right-derived-functor unit, and by the
K-injective criterion `Stacks.Cohomology.Localization.rightDerived_of_kInjectives` that in turn
comes down to one statement: for a K-injective complex `I` of `𝒪_X`-modules, the derivation unit
of abelian supported sections is invertible at the underlying complex `I_ab` of abelian sheaves.
That is the content of the source's argument, which goes through flasqueness: the underlying
abelian sheaf of an injective `𝒪_X`-module is flasque, and supported sections of a flasque
abelian sheaf over an open are the kernel of a surjection between sections over two opens, so a
complex of injective `𝒪_X`-modules computes `RH_Z` of the underlying complex of abelian sheaves
even though it is not a complex of injective abelian sheaves. Both inputs are proved in
`StacksFrontier/Topology/Sheaves/ClosedImmersion/FlasqueSupportedSections.lean` and `UnderlyingAbelianLocalCohomologyInvertible.lean`, the
latter concluding with `isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor`.
Note that the corresponding step of part (1) was different and easier: there the comparison was
reduced to Tag 0D5Y for sections over `X` and over `X ∖ Z`, and the supported sections were
recovered as the kernel of restriction. That reduction is not available at the sheaf level,
where `H_Z` is not a kernel of a map of functors already known to be comparable; what replaces
it is the same kernel description *after evaluation at each open*, which holds on flasque
sheaves.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Remark 17.5.4 (Tag 01AY)](https://stacks.math.columbia.edu/tag/01AY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.Localization (derivedUnit_isIsoOnKInjective rightDerived_of_kInjectives)
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-! ### The abelian supported-sections functor in the sheaf spelling -/

/-- The functor `H_Z : Ab(X) ⥤ Ab(Z)` of sections of an abelian sheaf supported on the closed
subset `Z`, with source and target spelled as sheaves for the Grothendieck topology of opens.
This is `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor` verbatim; only the spelling of
the two sheaf categories differs. -/
abbrev abelianSupportedSectionsOnClosed :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u} :=
  ClosedImmersionSheaves.supportedSectionsOnClosedFunctor Z hZ

/-- Abelian supported sections on a closed subset are additive, being a right adjoint. -/
instance abelianSupportedSectionsOnClosed_additive :
    (abelianSupportedSectionsOnClosed X Z hZ).Additive :=
  ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_additive Z hZ

/-- Forgetting the module structure and then taking abelian supported sections is additive. -/
instance forget_abelianSupportedSectionsOnClosed_additive :
    (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
      abelianSupportedSectionsOnClosed X Z hZ).Additive :=
  inferInstance

/-- **Stacks 0G6N, abelian compatibility**, in the sheaf spelling: forgetting the module
structure commutes with taking the sections supported on the closed subset `Z`, as functors
`Mod(𝒪_X) ⥤ Ab(Z)`. This is `supportedSectionsOnClosedForgetIso`; only the spelling of the
abelian sheaf categories differs. -/
def abelianSupportedSectionsOnClosedForgetIso :
    supportedSectionsOnClosedFunctor X Z hZ ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        abelianSupportedSectionsOnClosed X Z hZ := by
  exact supportedSectionsOnClosedForgetIso X Z hZ

/-! ### The comparison on homotopy categories -/

variable
  (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}))
  (aHab : (abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)

/-- The comparison on homotopy categories, built from the underived comparison of supported
sections and the derivation unit of a right derived functor of abelian supported sections. -/
def supportedSheafForgetUnit :
    ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
        underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ⟶
      DerivedCategory.Qh ⋙ (underlyingDerivedSheaf (structureSheafRing X) ⋙ RHab) :=
  Functor.whiskerLeft
      ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      (_root_.SheafOfModules.toSheaf
        (structureSheafRing (closedSubsetRingedSpace X Z))).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator
      ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      ((_root_.SheafOfModules.toSheaf
        (structureSheafRing (closedSubsetRingedSpace X Z))).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).inv ≫
    Functor.whiskerRight
      (@Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
        (abelianSupportedSectionsOnClosedForgetIso X Z hZ)
        (by exact supportedSectionsOnClosedFunctor_additive X Z hZ)
        (by exact inferInstanceAs
          (_root_.SheafOfModules.toSheaf
            (structureSheafRing (closedSubsetRingedSpace X Z))).Additive)
        (by exact forget_abelianSupportedSectionsOnClosed_additive X Z hZ)
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerRight
      (@Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
        (Iso.refl (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
          abelianSupportedSectionsOnClosed X Z hZ))
        (by exact inferInstanceAs (_root_.SheafOfModules.toSheaf (structureSheafRing X)).Additive)
        (by exact abelianSupportedSectionsOnClosed_additive X Z hZ)
        (by exact forget_abelianSupportedSectionsOnClosed_additive X Z hZ)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      ((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
        (ComplexShape.up ℤ)) aHab ≫
    Functor.whiskerRight
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.inv RHab

/-! ### The canonical comparison of Tag 0G74 (2) -/

variable
  (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))))
  (aH : (supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)

/-- The derivation unit of a right derived functor `RH_Z` of supported sections of modules,
composed with forgetting the module structure on the derived category of `𝒪_X|_Z`-modules. -/
def forgetfulSupportedSheafUnit :
    ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
        underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ⟶
      DerivedCategory.Qh ⋙
        (RH ⋙ underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X Z))) :=
  Functor.whiskerRight aH
      (underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X Z))) ≫
    (Functor.associator _ _ _).hom

/-- Forgetting the module structure on the derived category of `𝒪_X|_Z`-modules is exact, so it
carries a right derived functor of supported sections to one again. -/
instance isRightDerivedFunctor_forgetfulSupportedSheafUnit
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    (RH ⋙ underlyingDerivedSheaf
      (structureSheafRing (closedSubsetRingedSpace X Z))).IsRightDerivedFunctor
      (forgetfulSupportedSheafUnit X Z hZ RH aH)
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I _ => ?_)
  let := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RH aH I
  dsimp only [forgetfulSupportedSheafUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app]
  infer_instance

/-- **Stacks 0G74, part (2): the canonical map.** Let `Z` be a closed subset of a ringed space
`X`, let `RH` be a right derived functor of the sections supported on `Z` of sheaves of
`𝒪_X`-modules and `RHab` one of the sections supported on `Z` of abelian sheaves. This is the
canonical map `RH_Z(K)_ab ⟶ RH_Z(K_ab)` in `D(Ab(Z))`, natural in `K`, induced through the
universal property of `RH` by the underived comparison of supported sections.

This map is an isomorphism: `isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor`
in `UnderlyingAbelianLocalCohomologyInvertible.lean` proves it, for `aHab` the derivation unit of
a right derived functor of abelian supported sections. -/
@[stacks 0G74
  "part (2), the canonical map; invertibility is proved in \
  isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor"]
def localCohomologySheafForgetComparison
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    RH ⋙ underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X Z)) ⟶
      underlyingDerivedSheaf (structureSheafRing X) ⋙ RHab :=
  (RH ⋙ underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X Z))).rightDerivedDesc
    (forgetfulSupportedSheafUnit X Z hZ RH aH)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))
    _ (supportedSheafForgetUnit X Z hZ RHab aHab)

/-- The canonical map of Tag 0G74 (2) is pinned down by its composite with the derivation unit
of `RH_Z`: it is the unique transformation compatible with the underived comparison, so it does
not depend on a choice of resolutions. -/
lemma localCohomologySheafForgetComparison_fac
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    forgetfulSupportedSheafUnit X Z hZ RH aH ≫ Functor.whiskerLeft DerivedCategory.Qh
        (localCohomologySheafForgetComparison X Z hZ RHab aHab RH aH) =
      supportedSheafForgetUnit X Z hZ RHab aHab :=
  Functor.rightDerived_fac _ _ _ _ _

/-- The remaining content of Stacks 0G74 part (2), isolated: the canonical map is an isomorphism
exactly when the transported comparison `supportedSheafForgetUnit` exhibits
`K ↦ RH_Z(K_ab)` as a right derived functor of supported sections of `𝒪_X`-modules. -/
lemma isIso_localCohomologySheafForgetComparison
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))]
    (hd : (underlyingDerivedSheaf (structureSheafRing X) ⋙ RHab).IsRightDerivedFunctor
      (supportedSheafForgetUnit X Z hZ RHab aHab)
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))) :
    IsIso (localCohomologySheafForgetComparison X Z hZ RHab aHab RH aH) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (RH ⋙ underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X Z)))
    (forgetfulSupportedSheafUnit X Z hZ RH aH)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))
    _ (supportedSheafForgetUnit X Z hZ RHab aHab)).mp hd

/-- Both sides of the comparison of Tag 0G74 (2) have models, so the statement is not about an
empty family: total right derived functors exist for supported sections of modules and of
abelian sheaves alike, both categories being Grothendieck abelian. -/
lemma exists_rightDerivedFunctor_supportedSectionsOnClosed :
    ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)) ∧
      ((abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)) :=
  ⟨hasRightDerivedFunctor_moduleSheaves X _, hasRightDerivedFunctor_abelianSheaves X _⟩

end Stacks.Cohomology.SupportedComplexes

end
