module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.DegreewiseForgetExcisionSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyDerivedSquare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Classical module excision agrees with classical abelian excision, in every degree

Let `X` be a scheme, `T ⊆ X` a subset and `U ⊆ X` an open subscheme.  Local cohomology with
supports in `T` is local on `X` in two parallel senses: for `𝒪_X`-modules
(`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`) and for sheaves of
abelian groups (`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso`).
This file proves that the two agree, in every degree, across the forgetful functor:
`forget_localCohomologyRestrict_comm`.  The degree-zero case is
`Stacks.Cohomology.SupportedComplexes.forget_supportedSectionsRestrict_comm`.

## Main results

* `localCohomologyEndoForgetComparison`, `localCohomologyEndoForgetComparisonOpen`: the
  degree-`n` reading of [Stacks, Tag 0G74] part (2) at the supported-sections **endofunctor**
  spelling — the one both classical excisions use — together with
  `isIso_localCohomologyEndoForgetComparison`, that it is invertible for a closed `T`, and
  `localCohomologyEndoForgetIso`.
* `forgetExcisionDegreewiseSquare_crossed`: the degree-`n` square of [Stacks, Tag 0G87], with the
  crossing of the two spellings of "restrict and forget" carried as a morphism.
* `forget_localCohomologyRestrict_comm`: **the square, with the crossing cancelled.**

## Implementation notes

Everything from `moduleExcisionEndo` on is stated at one spelling of each functor, subset and
ambient space.  The alternatives are definitionally equal, but each reconciliation costs the
elaborator tens of thousands of heartbeats, and a statement that mixes spellings pays at every
occurrence; ascribing once, in `moduleExcisionEndo` and `abelianExcisionEndo`, keeps every
statement below within budget.  For the same reason the crossing is cancelled one end at a time,
through `degreewiseSquare_app_tail` and `degreewiseSquare_app_head`.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.9 (Tag 0G87)](https://stacks.math.columbia.edu/tag/0G87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedExcisionSquare
open Stacks.Cohomology.RestrictForgetComparison
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.LocalCohomologyExcision (supportedSectionsOn supportedSectionsRestrictNatIso
  localCohomologyOn localCohomologyRestrictNatIso)
open Stacks.SheafOfModules.SupportedSections (supportedSectionsFunctor)

universe u

namespace Stacks.Cohomology.DegreewiseExcisionSquare

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-! ### Extension by zero at the ascribed spellings -/

/-- **Extension by zero of modules**, with its source and target spelled as sheaves of modules
over the structure sheaf of the underlying ringed space.  This is
`Stacks.Cohomology.SupportedComplexes.moduleExtendByZero`; only the spelling of the two
categories differs, and the spelling is what the instances below are keyed on, exactly as for
`Stacks.Cohomology.RestrictForgetComparison.restrictModules`. -/
@[sga "2 VI 1.4" "Z open", sga "4 IV 11.3.1", sga "4 XVII 5.1.1"]
abbrev moduleExtendZero {X : Scheme.{u}} (U : X.Opens) :
    _root_.SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace) ⥤
      _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  moduleExtendByZero U

/-- Extension by zero of modules is additive, at the ascribed spelling. -/
instance moduleExtendZero_additive {X : Scheme.{u}} (U : X.Opens) :
    (moduleExtendZero U).Additive :=
  inferInstanceAs (moduleExtendByZero U).Additive

/-- Extension by zero of modules is left exact, at the ascribed spelling. -/
instance moduleExtendZero_preservesFiniteLimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (moduleExtendZero U) :=
  inferInstanceAs (PreservesFiniteLimits (moduleExtendByZero U))

/-- Extension by zero of modules is right exact, at the ascribed spelling. -/
instance moduleExtendZero_preservesFiniteColimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteColimits (moduleExtendZero U) :=
  inferInstanceAs (PreservesFiniteColimits (moduleExtendByZero U))

/-- **Extension by zero of abelian sheaves**, at the spellings of
`Stacks.Cohomology.RestrictForgetComparison.restrictAbelian`. -/
abbrev abelianExtendZero {X : Scheme.{u}} (U : X.Opens) :
    Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u} :=
  abelianExtendByZero (X := X.carrier) U

/-- Extension by zero of abelian sheaves is additive, at the ascribed spelling. -/
instance abelianExtendZero_additive {X : Scheme.{u}} (U : X.Opens) :
    (abelianExtendZero U).Additive :=
  inferInstanceAs (abelianExtendByZero (X := X.carrier) U).Additive

/-- Extension by zero of abelian sheaves is left exact, at the ascribed spelling. -/
instance abelianExtendZero_preservesFiniteLimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (abelianExtendZero U) :=
  inferInstanceAs (PreservesFiniteLimits (abelianExtendByZero (X := X.carrier) U))

/-- Extension by zero of abelian sheaves is right exact, at the ascribed spelling. -/
instance abelianExtendZero_preservesFiniteColimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteColimits (abelianExtendZero U) :=
  inferInstanceAs (PreservesFiniteColimits (abelianExtendByZero (X := X.carrier) U))

/-! ### The two restrictions preserve injectives, at the ascribed spellings -/

/-- **Restriction of modules to an open subscheme preserves injective objects**, at the spelling
`Stacks.Cohomology.RestrictForgetComparison.restrictModules`.  This is
`Stacks.Perfect.LocalCohomologyExcision.restrictFunctor_preservesInjectiveObjects`; instance
search does not cross the two spellings of the category of modules, so the ascription is made
once here. -/
instance restrictModules_preservesInjectiveObjects {X : Scheme.{u}} (U : X.Opens) :
    (restrictModules U).PreservesInjectiveObjects :=
  inferInstanceAs (Scheme.Modules.restrictFunctor U.ι).PreservesInjectiveObjects

/-- **Restriction of abelian sheaves to an open subset preserves injective objects**, at the
spelling `Stacks.Cohomology.RestrictForgetComparison.restrictAbelian`. -/
instance restrictAbelian_preservesInjectiveObjects {X : Scheme.{u}} (U : X.Opens) :
    (restrictAbelian U).PreservesInjectiveObjects :=
  inferInstanceAs (abelianRestrictOpen (X := X.carrier) U).PreservesInjectiveObjects

variable {X : Scheme.{u}} (T : Set X) (U : X.Opens)
  (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
  (aH : (supportedSectionsFunctor X.toRingedSpace T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
  (RHab : DerivedCategory
      (Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u}) ⥤
    DerivedCategory
      (Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u}))
  (aHab : (abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
  (RH' : DerivedCategory
      (_root_.SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace)))
  (aH' : (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH')
  (RHab' : DerivedCategory
      (Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u}) ⥤
    DerivedCategory
      (Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u}))
  (aHab' : (abelianSupportedSections (U.ι ⁻¹' T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab')
  [hRH : RH.IsRightDerivedFunctor aH
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))]
  [hRH' : RH'.IsRightDerivedFunctor aH'
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace))
      (ComplexShape.up ℤ))]
  [hRHab : RHab.IsRightDerivedFunctor aHab
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u})
      (ComplexShape.up ℤ))]
  [hRHab' : RHab'.IsRightDerivedFunctor aHab'
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u})
      (ComplexShape.up ℤ))]

/-- **The classical module excision is the degree-`n` reading of the derived module excision.**
`Stacks.DerivedIndexing.classicalExcision_bridge` at the excision datum of sheaves of modules:
the retyped `Stacks.Cohomology.DerivedExcisionSquare.moduleDerivedExcision` is the generic
`Stacks.DerivedIndexing.derivedExcisionNatIso`, both being
`CategoryTheory.Functor.rightDerivedNatIso` at the same two units with the same degreewise
input, and `Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` is the generic
classical excision. -/
theorem moduleExcision_bridge (n : ℕ) :
    Stacks.DerivedIndexing.singleHomologyMap
          (moduleDerivedExcision T U RH aH RH' aH').hom (n : ℤ) ≫
        (Stacks.DerivedIndexing.forgetLegTarget
          (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)) (restrictModules U)
          RH' aH' Stacks.Cohomology.Localization.enoughKInjectives n).hom =
      (Stacks.DerivedIndexing.forgetLegSource (supportedSectionsFunctor X.toRingedSpace T)
          (restrictModules U) RH aH Stacks.Cohomology.Localization.enoughKInjectives n).hom ≫
        (localCohomologyRestrictNatIso T U n).hom := by
  have := Stacks.DerivedIndexing.isRightDerivedFunctor_rightDerivedCompMapDerivedCategory
    (supportedSectionsFunctor X.toRingedSpace T) (restrictModules U) RH aH
    Stacks.Cohomology.Localization.enoughKInjectives
  have := Stacks.DerivedIndexing.isRightDerivedFunctor_mapDerivedCategoryCompRightDerived
    (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)) (restrictModules U) RH' aH'
    (moduleExtendZero U) (moduleExtendByZeroAdjunction U)
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives
  exact Stacks.DerivedIndexing.classicalExcision_bridge
    (supportedSectionsFunctor X.toRingedSpace T)
    (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)) (restrictModules U)
    (supportedSectionsRestrictNatIso T U) RH aH RH' aH'
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives n

/-- **The classical abelian excision is the degree-`n` reading of the derived abelian
excision**, the same statement on the other side of the square. -/
theorem abelianExcision_bridge (n : ℕ) :
    Stacks.DerivedIndexing.singleHomologyMap
          (abelianDerivedExcision T U RHab aHab RHab' aHab').hom (n : ℤ) ≫
        (Stacks.DerivedIndexing.forgetLegTarget (abelianSupportedSections (U.ι ⁻¹' T))
          (restrictAbelian U) RHab' aHab'
          Stacks.Cohomology.Localization.enoughKInjectives n).hom =
      (Stacks.DerivedIndexing.forgetLegSource (abelianSupportedSections T) (restrictAbelian U)
          RHab aHab Stacks.Cohomology.Localization.enoughKInjectives n).hom ≫
        (abelianLocalCohomologyRestrictNatIso (X := X.carrier) T U n).hom := by
  have := Stacks.DerivedIndexing.isRightDerivedFunctor_rightDerivedCompMapDerivedCategory
    (abelianSupportedSections T) (restrictAbelian U) RHab aHab
    Stacks.Cohomology.Localization.enoughKInjectives
  have := Stacks.DerivedIndexing.isRightDerivedFunctor_mapDerivedCategoryCompRightDerived
    (abelianSupportedSections (U.ι ⁻¹' T)) (restrictAbelian U) RHab' aHab'
    (abelianExtendZero U) (abelianExtendByZeroAdjunction U)
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives
  exact Stacks.DerivedIndexing.classicalExcision_bridge (abelianSupportedSections T)
    (abelianSupportedSections (U.ι ⁻¹' T)) (restrictAbelian U)
    (abelianSupportedSectionsRestrictNatIso (X := X.carrier) T U) RHab aHab RHab' aHab'
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives n

/-! ### The degree-`n` reading of [Stacks, Tag 0G74] part (2), at the endofunctor spelling -/

/-- **[Stacks, Tag 0G74] part (2) in degree `n`, at the supported-sections endofunctor
spelling.**  For a scheme `X`, a subset `T ⊆ X` and a degree `n`, the canonical map

`ℋ ⁿ_T(ℱ)_ab ⟶ ℋ ⁿ_T(ℱ_ab)`

of sheaves of abelian groups on `X`, natural in the `𝒪_X`-module `ℱ`, where both sides are
Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived` of the supported-sections
*endofunctor* — of `𝒪_X`-modules on the left and of abelian sheaves on the right.

`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorForgetIso` is the same reading
at the *on-closed-subset* spelling `Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)`, which is a different pair of
functors; this is the spelling the two classical excisions use, and the one the square of
[Stacks, Tag 0G87] needs.

It is `Stacks.DerivedIndexing.degreewiseForgetComparison` of
`Stacks.Cohomology.DerivedExcisionSquare.forgetComparison`, that is: the degree-`n` cohomology of
[Stacks, Tag 0G74] part (2) on the unbounded derived category, at a module placed in degree `0`,
read through the two bridges
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`.  For a closed `T` it is
invertible, by `isIso_localCohomologyEndoForgetComparison`. -/
def localCohomologyEndoForgetComparison (n : ℕ) :
    (supportedSectionsFunctor X.toRingedSpace T).rightDerived n ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace) ⟶
      _root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace) ⋙
        (abelianSupportedSections T).rightDerived n :=
  Stacks.DerivedIndexing.degreewiseForgetComparison (supportedSectionsFunctor X.toRingedSpace T)
    (abelianSupportedSections T)
    (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)) RH aH RHab aHab
    (forgetComparison T RH aH RHab aHab) Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives n

/-- **[Stacks, Tag 0G74] part (2) in degree `n` on the open subscheme `U`**, the same reading for
`U` and the preimage of `T`. -/
def localCohomologyEndoForgetComparisonOpen (n : ℕ) :
    (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)).rightDerived n ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace) ⟶
      _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace) ⋙
        (abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n :=
  Stacks.DerivedIndexing.degreewiseForgetComparison
    (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T))
    (abelianSupportedSections (U.ι ⁻¹' T))
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)) RH' aH'
    RHab' aHab' (forgetComparisonOpen T U RH' aH' RHab' aHab')
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives n

/-- **For a closed `T` the degree-`n` comparison is invertible.**  [Stacks, Tag 0G74] part (2)
on the unbounded derived category is invertible for a closed subset, by
`Stacks.Cohomology.AbelianSupportedCounitForget.isIso_abelianSupportedEndoForgetComparison`, and
the degree-`n` reading of an invertible comparison is invertible. -/
theorem isIso_localCohomologyEndoForgetComparison (hT : IsClosed T) (n : ℕ) :
    IsIso (localCohomologyEndoForgetComparison T RH aH RHab aHab n) := by
  have : IsIso (forgetComparison T RH aH RHab aHab) :=
    Stacks.Cohomology.AbelianSupportedCounitForget.isIso_abelianSupportedEndoForgetComparison
      X.toRingedSpace T RHab aHab RH aH hT
  change IsIso (Stacks.DerivedIndexing.degreewiseForgetComparison
    (supportedSectionsFunctor X.toRingedSpace T) (abelianSupportedSections T)
    (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)) RH aH RHab aHab
    (forgetComparison T RH aH RHab aHab) Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives n)
  rw [← Stacks.DerivedIndexing.degreewiseForgetIso_hom]
  infer_instance

/-- **[Stacks, Tag 0G74] part (2) in degree `n`, as an isomorphism**, for a closed `T`:

`ℋ ⁿ_T(ℱ)_ab ≅ ℋ ⁿ_T(ℱ_ab)`,

naturally in the `𝒪_X`-module `ℱ`, at the supported-sections endofunctor spelling. -/
def localCohomologyEndoForgetIso (hT : IsClosed T) (n : ℕ) :
    (supportedSectionsFunctor X.toRingedSpace T).rightDerived n ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace) ⋙
        (abelianSupportedSections T).rightDerived n :=
  haveI := isIso_localCohomologyEndoForgetComparison T RH aH RHab aHab hT n
  asIso (localCohomologyEndoForgetComparison T RH aH RHab aHab n)

/-! ### The underived crossing, in the shape the pair coherence produces -/

/-- The underived crossing of the two spellings of "restrict and forget", written as the
composite the coherence of a pair of composition comparisons produces.  It is the identity: both
factors are, `Stacks.Cohomology.RestrictForgetComparison.restrictForgetIso` being
`CategoryTheory.Iso.refl`. -/
abbrev pairCrossing :
    restrictModules U ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace) ⋙ restrictAbelian U :=
  Iso.refl (restrictModules U ⋙
      _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)) ≪≫
    (restrictForgetIso U).symm.symm

/-- **The derived crossing of the two spellings of "restrict and forget", written as the pair of
composition comparisons it is.**  This is
`Stacks.Cohomology.RestrictForgetComparison.derivedRestrictCompToSheafIso` — see
`pairDerivedCrossing_eq` — written as a `reducible` abbreviation, so that the two crossing
coherences below unify with `Stacks.DerivedIndexing.crossingPair_single` and
`..crossingPair_homology` without a `def` having to be unfolded at these concrete derived
categories. -/
abbrev pairDerivedCrossing :
    (restrictModules U).mapDerivedCategory ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapDerivedCategory ⋙
        (restrictAbelian U).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (restrictModules U ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso (restrictForgetIso U).symm).symm

/-- `pairDerivedCrossing` is the library's derived crossing. -/
theorem pairDerivedCrossing_eq : pairDerivedCrossing U = derivedRestrictCompToSheafIso U := rfl

/-- The crossing is the identity. -/
theorem pairCrossing_hom :
    (pairCrossing U).hom =
      CategoryStruct.id (restrictModules U ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)) :=
  Category.id_comp _

/-- **The derived crossing agrees with the underived one on an object placed in degree `0`.**
`Stacks.DerivedIndexing.crossingPair_single` at the two composition comparisons
`Stacks.Cohomology.RestrictForgetComparison.derivedRestrictCompToSheafIso` is built from. -/
theorem crossing_single :
    Functor.whiskerLeft
          (DerivedCategory.singleFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0)
          (pairDerivedCrossing U).hom ≫
        Functor.whiskerRight
            ((_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapDerivedCategorySingleFunctor 0).hom
            (restrictAbelian U).mapDerivedCategory ≫
          Functor.whiskerLeft
            (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace))
            ((restrictAbelian U).mapDerivedCategorySingleFunctor 0).hom =
      Functor.whiskerRight ((restrictModules U).mapDerivedCategorySingleFunctor 0).hom
          (_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ≫
        Functor.whiskerLeft (restrictModules U)
            ((_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategorySingleFunctor
                0).hom ≫
          Functor.whiskerRight (pairCrossing U).hom
            (DerivedCategory.singleFunctor
              (Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier)
                AddCommGrpCat.{u}) 0) :=
  Stacks.DerivedIndexing.crossingPair_single (restrictModules U)
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))
    (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)) (restrictAbelian U)
    (restrictModules U ⋙
      _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))
    (Iso.refl _) (restrictForgetIso U).symm

/-- **The derived crossing agrees with the underived one on degree-`n` cohomology.**
`Stacks.DerivedIndexing.crossingPair_homology` at the same two composition comparisons. -/
theorem crossing_homology (m : ℤ) :
    Functor.whiskerRight (pairDerivedCrossing U).hom
          (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier)
              AddCommGrpCat.{u}) m) ≫
        Functor.whiskerLeft
            (_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapDerivedCategory
            ((restrictAbelian U).mapDerivedCategoryHomologyIso m).hom ≫
          Functor.whiskerRight
            ((_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapDerivedCategoryHomologyIso m).hom
            (restrictAbelian U) =
      Functor.whiskerLeft (restrictModules U).mapDerivedCategory
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryHomologyIso m).hom ≫
        Functor.whiskerRight ((restrictModules U).mapDerivedCategoryHomologyIso m).hom
            (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)) ≫
          Functor.whiskerLeft
            (DerivedCategory.homologyFunctor
              (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) m)
            (pairCrossing U).hom :=
  Stacks.DerivedIndexing.crossingPair_homology (restrictModules U)
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))
    (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)) (restrictAbelian U)
    (restrictModules U ⋙
      _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))
    (Iso.refl _) (restrictForgetIso U).symm m


/-- **The derived square of [Stacks, Tag 0G87] with the crossing written as the pair.**  This is
`Stacks.Cohomology.DerivedExcisionSquare.forgetExcisionDerivedSquare`, with its two sides written
out and the crossing presented as `pairDerivedCrossing`. -/
theorem derivedSquare_pair :
    Functor.whiskerRight (moduleDerivedExcision T U RH aH RH' aH').hom
          (_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ≫
        Functor.whiskerLeft (restrictModules U).mapDerivedCategory
            (forgetComparisonOpen T U RH' aH' RHab' aHab') ≫
          Functor.whiskerRight (pairDerivedCrossing U).hom RHab' =
      Functor.whiskerLeft RH (pairDerivedCrossing U).hom ≫
        Functor.whiskerRight (forgetComparison T RH aH RHab aHab)
            (restrictAbelian U).mapDerivedCategory ≫
          Functor.whiskerLeft
            (_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapDerivedCategory
            (abelianDerivedExcision T U RHab aHab RHab' aHab').hom :=
  forgetExcisionDerivedSquare T U RH aH RHab aHab RH' aH' RHab' aHab'

/-! ### The two classical excisions at the supported-sections endofunctor spelling -/

/-- **The classical module excision, at the spelling the degree-`n` square speaks.**  This is
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` — see
`moduleExcisionEndo_eq` — with `ℋ ⁿ_T` written as the `ℕ`-indexed right derived functor of the
supported-sections *endofunctor* rather than as
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn`, and the restriction written as
`Stacks.Cohomology.RestrictForgetComparison.restrictModules`.

The ascription is made once, here, and everything below speaks this one spelling.  The two
spellings of the ambient space of `U`, of the preimage of `T` in it, and of `ℋ ⁿ` are all
definitionally equal, but reconciling them costs the elaborator real work, and a statement that
mixes them pays for it at every occurrence. -/
def moduleExcisionEndo (n : ℕ) :
    (supportedSectionsFunctor X.toRingedSpace T).rightDerived n ⋙ restrictModules U ≅
      restrictModules U ⋙
        (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)).rightDerived n :=
  localCohomologyRestrictNatIso T U n

/-- `moduleExcisionEndo` **is** the classical module excision. -/
theorem moduleExcisionEndo_eq (n : ℕ) :
    moduleExcisionEndo T U n = localCohomologyRestrictNatIso T U n :=
  rfl

/-- **The classical abelian excision, at the same spelling.**  This is
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso` — see
`abelianExcisionEndo_eq` — with the ambient space of `U` spelled as that of the open subscheme
and the preimage of `T` as `U.ι ⁻¹' T` rather than
`Stacks.Cohomology.SupportedComplexes.preimageSubset`. -/
def abelianExcisionEndo (n : ℕ) :
    (abelianSupportedSections T).rightDerived n ⋙ restrictAbelian U ≅
      restrictAbelian U ⋙ (abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n :=
  abelianLocalCohomologyRestrictNatIso (X := X.carrier) T U n

/-- `abelianExcisionEndo` **is** the classical abelian excision. -/
theorem abelianExcisionEndo_eq (n : ℕ) :
    abelianExcisionEndo T U n =
      abelianLocalCohomologyRestrictNatIso (X := X.carrier) T U n :=
  rfl

/-- `moduleExcision_bridge` at the ascribed spelling. -/
theorem moduleExcisionEndo_bridge (n : ℕ) :
    Stacks.DerivedIndexing.singleHomologyMap
          (moduleDerivedExcision T U RH aH RH' aH').hom (n : ℤ) ≫
        (Stacks.DerivedIndexing.forgetLegTarget
          (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)) (restrictModules U)
          RH' aH' Stacks.Cohomology.Localization.enoughKInjectives n).hom =
      (Stacks.DerivedIndexing.forgetLegSource (supportedSectionsFunctor X.toRingedSpace T)
          (restrictModules U) RH aH Stacks.Cohomology.Localization.enoughKInjectives n).hom ≫
        (moduleExcisionEndo T U n).hom :=
  moduleExcision_bridge T U RH aH RH' aH' n

/-- `abelianExcision_bridge` at the ascribed spelling. -/
theorem abelianExcisionEndo_bridge (n : ℕ) :
    Stacks.DerivedIndexing.singleHomologyMap
          (abelianDerivedExcision T U RHab aHab RHab' aHab').hom (n : ℤ) ≫
        (Stacks.DerivedIndexing.forgetLegTarget (abelianSupportedSections (U.ι ⁻¹' T))
          (restrictAbelian U) RHab' aHab'
          Stacks.Cohomology.Localization.enoughKInjectives n).hom =
      (Stacks.DerivedIndexing.forgetLegSource (abelianSupportedSections T) (restrictAbelian U)
          RHab aHab Stacks.Cohomology.Localization.enoughKInjectives n).hom ≫
        (abelianExcisionEndo T U n).hom :=
  abelianExcision_bridge T U RHab aHab RHab' aHab' n

/-! ### The degree-`n` square -/

/-- **The degree-`n` square of [Stacks, Tag 0G87], with the crossing of the two spellings of
"restrict and forget" carried as a morphism.**  This is
`Stacks.DerivedIndexing.forgetExcisionDegreewiseSquare` at the two excision data of this chapter:
the derived square `Stacks.Cohomology.DerivedExcisionSquare.forgetExcisionDerivedSquare` supplies
the hypothesis on total derived functors, the two bridges above identify each derived excision
with its classical form, and `Stacks.DerivedIndexing.crossingPair_single` and
`..crossingPair_homology` identify the derived crossing with the underived one at an object placed
in degree `0` and on cohomology.

The crossing is the identity, by `pairCrossing_hom`; it is cancelled in
`forget_localCohomologyRestrict_comm`. -/
theorem forgetExcisionDegreewiseSquare_crossed (n : ℕ) :
    Functor.whiskerRight (moduleExcisionEndo T U n).hom
          (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)) ≫
        Functor.whiskerLeft (restrictModules U)
            (localCohomologyEndoForgetComparisonOpen T U RH' aH' RHab' aHab' n) ≫
          Functor.whiskerRight (pairCrossing U).hom
            ((abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n) =
      Functor.whiskerLeft
            ((supportedSectionsFunctor X.toRingedSpace T).rightDerived n) (pairCrossing U).hom ≫
        Functor.whiskerRight (localCohomologyEndoForgetComparison T RH aH RHab aHab n)
            (restrictAbelian U) ≫
          Functor.whiskerLeft
            (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace))
            (abelianExcisionEndo T U n).hom :=
  Stacks.DerivedIndexing.forgetExcisionDegreewiseSquare
    (supportedSectionsFunctor X.toRingedSpace T)
    (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T))
    (abelianSupportedSections T) (abelianSupportedSections (U.ι ⁻¹' T))
    (restrictModules U) (restrictAbelian U)
    (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace))
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))
    RH aH RH' aH' RHab aHab RHab' aHab'
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives n
    (moduleDerivedExcision T U RH aH RH' aH')
    (abelianDerivedExcision T U RHab aHab RHab' aHab')
    (forgetComparison T RH aH RHab aHab) (forgetComparisonOpen T U RH' aH' RHab' aHab')
    (pairDerivedCrossing U) (pairCrossing U)
    (moduleExcisionEndo T U n) (abelianExcisionEndo T U n)
    (moduleExcisionEndo_bridge T U RH aH RH' aH' n)
    (abelianExcisionEndo_bridge T U RHab aHab RHab' aHab' n)
    (crossing_single U) (crossing_homology U (n : ℤ))
    (derivedSquare_pair T U RH aH RHab aHab RH' aH' RHab' aHab')

/-! ### Cancelling the crossing -/

/-- **The crossing is the identity at every module**, `pairCrossing_hom` read at a component. -/
theorem pairCrossing_hom_app
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (pairCrossing U).hom.app F =
      CategoryStruct.id ((restrictModules U ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).obj F) :=
  NatTrans.congr_app (pairCrossing_hom U) F

/-- The crossing is the identity at the degree-`n` local cohomology of a module. -/
theorem pairCrossing_hom_app_localCohomology (n : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (pairCrossing U).hom.app
        (((supportedSectionsFunctor X.toRingedSpace T).rightDerived n).obj F) =
      CategoryStruct.id ((restrictModules U ⋙
          _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).obj
        (((supportedSectionsFunctor X.toRingedSpace T).rightDerived n).obj F)) :=
  pairCrossing_hom_app U _

/-- The degree-`n` abelian local cohomology sheaf of the crossing is the identity. -/
theorem localCohomology_map_pairCrossing_hom_app (n : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    ((abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n).map
        ((pairCrossing U).hom.app F) =
      CategoryStruct.id
        (((abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n).obj
          ((restrictModules U ⋙
            _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).obj
              F)) :=
  (congrArg ((abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n).map
      (pairCrossing_hom_app U F)).trans
    (((abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n).map_id _)

/-- The crossing cancels off the tail of the module side of the square. -/
theorem degreewiseSquare_app_tail (n : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((moduleExcisionEndo T U n).hom.app F) ≫
        (localCohomologyEndoForgetComparisonOpen T U RH' aH' RHab' aHab' n).app
            ((restrictModules U).obj F) ≫
          ((abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n).map
            ((pairCrossing U).hom.app F) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((moduleExcisionEndo T U n).hom.app F) ≫
        (localCohomologyEndoForgetComparisonOpen T U RH' aH' RHab' aHab' n).app
          ((restrictModules U).obj F) :=
  (congrArg (fun t =>
      (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((moduleExcisionEndo T U n).hom.app F) ≫
        (localCohomologyEndoForgetComparisonOpen T U RH' aH' RHab' aHab' n).app
            ((restrictModules U).obj F) ≫ t)
    (localCohomology_map_pairCrossing_hom_app T U n F)).trans
    (congrArg (fun t =>
        (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((moduleExcisionEndo T U n).hom.app F) ≫ t)
      (Category.comp_id
        ((localCohomologyEndoForgetComparisonOpen T U RH' aH' RHab' aHab' n).app
          ((restrictModules U).obj F))))

/-- The crossing cancels off the head of the abelian side of the square. -/
theorem degreewiseSquare_app_head (n : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (pairCrossing U).hom.app
          (((supportedSectionsFunctor X.toRingedSpace T).rightDerived n).obj F) ≫
        (restrictAbelian U).map
            ((localCohomologyEndoForgetComparison T RH aH RHab aHab n).app F) ≫
          (abelianExcisionEndo T U n).hom.app
            ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F) =
      (restrictAbelian U).map
          ((localCohomologyEndoForgetComparison T RH aH RHab aHab n).app F) ≫
        (abelianExcisionEndo T U n).hom.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F) :=
  (congrArg (fun t => t ≫
      (restrictAbelian U).map
          ((localCohomologyEndoForgetComparison T RH aH RHab aHab n).app F) ≫
        (abelianExcisionEndo T U n).hom.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F))
    (pairCrossing_hom_app_localCohomology T U n F)).trans
    (Category.id_comp
      ((restrictAbelian U).map
          ((localCohomologyEndoForgetComparison T RH aH RHab aHab n).app F) ≫
        (abelianExcisionEndo T U n).hom.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F)))

/-- `forgetExcisionDegreewiseSquare_crossed` read at a module. -/
theorem degreewiseSquare_app (n : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((moduleExcisionEndo T U n).hom.app F) ≫
        (localCohomologyEndoForgetComparisonOpen T U RH' aH' RHab' aHab' n).app
            ((restrictModules U).obj F) ≫
          ((abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n).map
            ((pairCrossing U).hom.app F) =
      (pairCrossing U).hom.app
            (((supportedSectionsFunctor X.toRingedSpace T).rightDerived n).obj F) ≫
        (restrictAbelian U).map
            ((localCohomologyEndoForgetComparison T RH aH RHab aHab n).app F) ≫
          (abelianExcisionEndo T U n).hom.app
            ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F) :=
  NatTrans.congr_app
    (forgetExcisionDegreewiseSquare_crossed T U RH aH RHab aHab RH' aH' RHab' aHab' n) F

/-- The same with the head crossing cancelled. -/
theorem degreewiseSquare_app_of_head (n : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((moduleExcisionEndo T U n).hom.app F) ≫
        (localCohomologyEndoForgetComparisonOpen T U RH' aH' RHab' aHab' n).app
            ((restrictModules U).obj F) ≫
          ((abelianSupportedSections (U.ι ⁻¹' T)).rightDerived n).map
            ((pairCrossing U).hom.app F) =
      (restrictAbelian U).map
          ((localCohomologyEndoForgetComparison T RH aH RHab aHab n).app F) ≫
        (abelianExcisionEndo T U n).hom.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F) :=
  (degreewiseSquare_app T U RH aH RHab aHab RH' aH' RHab' aHab' n F).trans
    (degreewiseSquare_app_head T U RH aH RHab aHab n F)

/-- **In every degree `n`, classical module excision for local cohomology agrees with classical
abelian excision, across the forgetful functor.**

For a scheme `X`, a subset `T ⊆ X`, an open subscheme `U ⊆ X`, a degree `n` and an `𝒪_X`-module
`ℱ`, the square

`ℋ ⁿ_T(ℱ)|_U ⟶ ℋ ⁿ_{U ∩ T}(ℱ|_U)` read on abelian sheaves, versus
`ℋ ⁿ_T(ℱ_ab)|_U ⟶ ℋ ⁿ_{U ∩ T}(ℱ_ab|_U)`,

commutes: the classical module excision
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` — here
`moduleExcisionEndo`, which is it, by `moduleExcisionEndo_eq` — carried along the forgetful
functor to sheaves of abelian groups by the degree-`n` reading
`localCohomologyEndoForgetComparisonOpen` of [Stacks, Tag 0G74] part (2) on `U`, is the classical
abelian excision `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso` —
here `abelianExcisionEndo`, by `abelianExcisionEndo_eq` — read through that same comparison
`localCohomologyEndoForgetComparison` on `X`.

That the equation is well-typed is the underived identity
`Stacks.Cohomology.SupportedComplexes.forgetRestrictCompIso`: restricting a module to `U` and
forgetting *is* forgetting and restricting the abelian sheaf, so the source of the left-hand side
is the source of the right-hand side and likewise for the two targets, and no crossing morphism
is needed — exactly as in the degree-zero statement
`Stacks.Cohomology.SupportedComplexes.forget_supportedSectionsRestrict_comm`, of which this is
the general-degree form.

No closedness assumption on `T` is needed: the two excisions and the two degree-`n` comparisons
all exist for an arbitrary subset.  For a closed `T` the comparisons are invertible, by
`isIso_localCohomologyEndoForgetComparison`, and the statement then says that the module excision
*is* the abelian excision conjugated by them.

This is `forgetExcisionDegreewiseSquare_crossed` with the crossing cancelled at each end — it is
the identity, by `pairCrossing_hom`. -/
theorem forget_localCohomologyRestrict_comm (n : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((moduleExcisionEndo T U n).hom.app F) ≫
        (localCohomologyEndoForgetComparisonOpen T U RH' aH' RHab' aHab' n).app
          ((restrictModules U).obj F) =
      (restrictAbelian U).map
          ((localCohomologyEndoForgetComparison T RH aH RHab aHab n).app F) ≫
        (abelianExcisionEndo T U n).hom.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F) :=
  (degreewiseSquare_app_tail T U RH' aH' RHab' aHab' n F).symm.trans
    (degreewiseSquare_app_of_head T U RH aH RHab aHab RH' aH' RHab' aHab' n F)

end Stacks.Cohomology.DegreewiseExcisionSquare

end
