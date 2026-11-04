module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetUnits
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompIsoSpellings
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianLocalCohomologyDerivedExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedCounitForget
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionCocycle
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.DerivedRestrictForgetComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedExcision
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0G74(2) commutes with both excisions, on the unbounded derived category

Let `X` be a scheme, `T ⊆ X` a subset and `U ⊆ X` an open subscheme with inclusion `j : U → X`.
There are four comparisons of total right derived functors in play:

* [Stacks, Tag 0G74] part (2) on `X` — forgetting the module structure past `R𝓗_T`, which is
  `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`;
* the same on `U`;
* derived-category excision for modules,
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsRestrictNatIso`;
* derived-category excision for abelian sheaves,
  `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsRestrictNatIso`.

This file proves the square they form, read through the comparison
`Stacks.Cohomology.RestrictForgetComparison.derivedRestrictCompToSheafIso` of the two spellings of
"restrict and forget" on derived categories.  It is the derived-category half of the square that
[Stacks, Tag 0G87] needs, and it is what the degree-`n` coherence recorded as missing in the
implementation notes of
`Stacks.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyExcision` is to be read off:
the classical module excision
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` and the classical abelian
excision `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso` are the
degree-`n` cohomology of the two derived excisions here, by
`Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision`, so the degree-`n` square follows
from this one once the degree-`n` reading of [Stacks, Tag 0G74] part (2) at the
supported-sections *endofunctor* spelling is in place.  That reading does not exist in the library
yet: `Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorForgetIso` is the degreewise
comparison at the *on-closed-subset* spelling `Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)`, not at the endofunctor
spelling the two excisions use, and nothing in the library composes the two.

## Main definitions

* `Stacks.Cohomology.DerivedExcisionSquare.moduleDerivedExcision`,
  `..abelianDerivedExcision`, `..forgetComparison` and `..forgetComparisonOpen`: the four
  comparisons, each retyped at the spellings of
  `Stacks.Cohomology.RestrictForgetComparison`, so that they compose.
* `Stacks.Cohomology.DerivedExcisionSquare.restrictUnit` and `..restrictForgetUnit`: the
  derivation units exhibiting `R𝓗_T ⋙ (-)|_U^D` and `R𝓗_T ⋙ (-)|_U^D ⋙ Φ_U^D` as right derived
  functors.
* `Stacks.Cohomology.DerivedExcisionSquare.excisionThenForget` and `..forgetThenExcision`: the
  two sides of the square.
* `Stacks.Cohomology.DerivedExcisionSquare.moduleExcisionHomotopyIso` and
  `..abelianExcisionHomotopyIso`: the two degree-zero excisions read on the homotopy category,
  before `DerivedCategory.Qh`; the library's
  `Stacks.Cohomology.SupportedComplexes.supportedSectionsRestrictHomotopyIso` and
  `...abelianSupportedSectionsRestrictHomotopyIso` are these whiskered with it.

## Main results

* `Stacks.Cohomology.DerivedExcisionSquare.isRightDerivedFunctor_restrictForget`: that composite
  **is** a right derived functor, with that unit.  Restriction to an open subscheme and the
  forgetful functor are both exact, so this is two applications of
  `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`.
* `Stacks.Cohomology.DerivedExcisionSquare.forgetExcisionSquare_app` and
  `..forgetExcisionHomotopySquare`: the degree-zero square of [Stacks, Tag 0G87] with the
  crossing of the two spellings carried as a morphism, at one module and then on the homotopy
  category of cochain complexes.
* `Stacks.Cohomology.DerivedExcisionSquare.crossing_Qh`: the comparison of the two spellings of
  "restrict and forget" on derived categories, read from the homotopy category.
* `Stacks.Cohomology.DerivedExcisionSquare.forgetExcisionDerivedSquare`: **the square commutes.**

## Implementation notes

**Four spellings, reconciled once.**  The four comparisons are stated in the library at four
mutually definitionally equal but syntactically distinct spellings of the categories involved:
the module excision at `AlgebraicGeometry.Scheme.Modules`, the forgetful comparison at
`SheafOfModules (structureSheafRing _)`, the abelian excision at
`Opens.grothendieckTopology ((Opens.toTopCat X.carrier).obj U)` and the forgetful comparison on
`U` at `Opens.grothendieckTopology ↥U.toRingedSpace.carrier`.  Instance search is keyed on the
syntax and does not cross between them, so each comparison is retyped here once, at the spellings
of `Stacks.Cohomology.RestrictForgetComparison.restrictModules` and
`Stacks.Cohomology.RestrictForgetComparison.restrictAbelian`, and all four then compose.

What the retyping needs is the class `CategoryTheory.Functor.IsRightDerivedFunctor`, whose own
statement carries a `CategoryTheory.Functor.IsLocalization` instance argument; at a mixed spelling
that argument is not found by instance search, so the three `qh_isLocalization_*` bridges supply
it.  They are plain theorems rather than instances: as instances they would match their own
hypothesis, the two morphism properties being definitionally equal.  Supplying one by a `letI` is
not enough on its own: the class is keyed on the spelling of the morphism property, and
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsOn` is a plain `def`, so instance search
at the mixed spelling cannot unfold it and the hypothesis has to be handed over by an explicit
`@`-application.

**Every chase is a helper at a variable category, applied with `exact`.**  `chaseA` and `chaseB`
are the two reductions after the derivation unit, `star2_chase` the assembly of the localized
degree-zero square, and the rest are the single moves.  At the concrete derived categories the
objects along each chain have two definitionally equal spellings — `(H_T ⋙ (-)|_U)^h K` versus
`(-)|_U^h (H_T^h K)`, and `Φ_U^D(Qh K)` versus `Qh(Φ_U^h K)` — and
`HomologicalComplexUpToQuasiIso.Qh` is not `@[expose]`, so a rewrite whose motive mentions them is
not type-correct.  A functor's `map` is never rewritten under: `congrArg` on a separately proved
equation is used instead.

**No `@[stacks ...]` attribute is attached to any declaration here.**  The square is a component
of [Stacks, Tag 0G87], and a tag attribute is not placed on a component.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RestrictForgetComparison
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.AbelianSupportedCounit (abelianSupportedSectionsForgetIso
  abelianSupportedEndoForgetComparison abelianSupportedEndoForgetComparison_fac
  forgetfulSupportedEndoUnit abelianSupportedEndoForgetUnit)
open Stacks.Cohomology.AbelianSupportedCounitForget (forgetCompIso)
open Stacks.Perfect.LocalCohomologyExcision (supportedSectionsOn supportedSectionsRestrictNatIso)
open Stacks.SheafOfModules.SupportedSections (supportedSectionsFunctor)

universe u

namespace Stacks.Cohomology.DerivedExcisionSquare

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-! ### The three localization bridges -/

/-- **`DerivedCategory.Qh` for sheaves of modules on a scheme localizes the quasi-isomorphisms, at
the `AlgebraicGeometry.Scheme.Modules` spelling of the morphism property.**

`CategoryTheory.Functor.IsRightDerivedFunctor` takes a `CategoryTheory.Functor.IsLocalization`
instance argument, so a statement of it mixing the two spellings of the category of modules cannot
even be elaborated without this. -/
theorem qh_isLocalization_schemeModules (X : Scheme.{u}) :
    (DerivedCategory.Qh (C := _root_.SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace))).IsLocalization
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  inferInstanceAs ((DerivedCategory.Qh (C := _root_.SheafOfModules.{u}
      (structureSheafRing X.toRingedSpace))).IsLocalization
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)))

/-- The same bridge for the modules on an open subscheme, where the two spellings are
`AlgebraicGeometry.Scheme.Modules ↥U` and
`SheafOfModules (structureSheafRing ↥U.toRingedSpace)`. -/
theorem qh_isLocalization_openModules {X : Scheme.{u}} (U : X.Opens) :
    (DerivedCategory.Qh (C := _root_.SheafOfModules.{u}
        (structureSheafRing U.toScheme.toRingedSpace))).IsLocalization
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ)) :=
  inferInstanceAs ((DerivedCategory.Qh (C := _root_.SheafOfModules.{u}
      (structureSheafRing U.toScheme.toRingedSpace))).IsLocalization
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace))
      (ComplexShape.up ℤ)))

/-- The same bridge for the abelian sheaves on an open subscheme, where the two spellings of its
space are `↥U.toRingedSpace.carrier` and `(Opens.toTopCat X.toRingedSpace.carrier).obj U`. -/
theorem qh_isLocalization_openAbelian {X : Scheme.{u}} (U : X.Opens) :
    (DerivedCategory.Qh (C := Sheaf
        (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier)
        AddCommGrpCat.{u})).IsLocalization
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U)) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  inferInstanceAs ((DerivedCategory.Qh (C := Sheaf
      (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier)
      AddCommGrpCat.{u})).IsLocalization
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)))

/-! ### The data -/

section Data

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

/-- **Derived-category excision for the local cohomology of sheaves of modules**, retyped at the
spelling `Stacks.Cohomology.RestrictForgetComparison.restrictModules` of restriction.  This is
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsRestrictNatIso`; the two
`CategoryTheory.Functor.IsRightDerivedFunctor` hypotheses are transported across the two
spellings of the category of modules by `qh_isLocalization_schemeModules` and
`qh_isLocalization_openModules`. -/
@[sga "4 V 6.4" "Clause 1), special case"]
def moduleDerivedExcision
    [hRH : RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ))]
    [hRH' : RH'.IsRightDerivedFunctor aH'
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace))
        (ComplexShape.up ℤ))] :
    RH ⋙ (restrictModules U).mapDerivedCategory ≅
      (restrictModules U).mapDerivedCategory ⋙ RH' :=
  letI := qh_isLocalization_schemeModules X
  letI := qh_isLocalization_openModules U
  @derivedSupportedSectionsRestrictNatIso _ T U RH aH RH' aH' hRH hRH'

/-- **Derived-category excision for the local cohomology of sheaves of abelian groups**, retyped
at the spelling `Stacks.Cohomology.RestrictForgetComparison.restrictAbelian` of restriction.  This
is `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsRestrictNatIso` at the
underlying space of the ringed space of `X`, with the hypothesis on `RHab'` transported across the
two spellings of the space of `U` by `qh_isLocalization_openAbelian`. -/
def abelianDerivedExcision
    [hRHab : RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [hRHab' : RHab'.IsRightDerivedFunctor aHab'
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))] :
    RHab ⋙ (restrictAbelian U).mapDerivedCategory ≅
      (restrictAbelian U).mapDerivedCategory ⋙ RHab' :=
  letI := qh_isLocalization_openAbelian U
  @derivedAbelianSupportedSectionsRestrictNatIso X.toRingedSpace.carrier T U
    RHab aHab RHab' aHab' hRHab hRHab'

/-- **[Stacks, Tag 0G74] part (2) on `X`, on the unbounded derived category**: the canonical map
`(R𝓗_T K)_ab ⟶ R𝓗_T^{ab}(K_ab)` of endofunctors of the derived categories.  This is
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison` at the underlying
ringed space of `X`, with no retyping needed. -/
def forgetComparison
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ))] :
    RH ⋙ (_root_.SheafOfModules.toSheaf
        (structureSheafRing X.toRingedSpace)).mapDerivedCategory ⟶
      (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapDerivedCategory ⋙
        RHab :=
  Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison
    X.toRingedSpace T RHab aHab RH aH

/-- **[Stacks, Tag 0G74] part (2) on `U`**, the same comparison for the open subscheme and the
preimage of `T`. -/
def forgetComparisonOpen
    [RH'.IsRightDerivedFunctor aH'
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace))
        (ComplexShape.up ℤ))] :
    RH' ⋙ (_root_.SheafOfModules.toSheaf
        (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ⟶
      (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ⋙ RHab' :=
  Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison
    U.toScheme.toRingedSpace (U.ι ⁻¹' T) RHab' aHab' RH' aH'

end Data

/-! ### The degree-zero square, with the crossing of the two spellings carried -/

section DegreeZero

variable {X : Scheme.{u}} (T : Set X) (U : X.Opens)

/-- **The degree-zero square of [Stacks, Tag 0G87] at one `𝒪_X`-module, with the crossing of the
two spellings of "restrict and forget" carried as a morphism.**

This is `Stacks.Cohomology.SupportedComplexes.forget_supportedSectionsRestrict_comm` with the
two components of `Stacks.Cohomology.RestrictForgetComparison.restrictForgetIso` inserted; that
isomorphism is `CategoryTheory.Iso.refl`, so the two components are identities and nothing is
added mathematically.  Carrying them is what makes the statement compose with the
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` readings of the four comparisons, in which
the crossing is a named morphism rather than a definitional identification. -/
theorem forgetExcisionSquare_app
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((supportedSectionsRestrictNatIso T U).hom.app F) ≫
        (abelianSupportedSectionsForgetIso U.toScheme.toRingedSpace (U.ι ⁻¹' T)).hom.app
            ((restrictModules U).obj F) ≫
          (abelianSupportedSections (U.ι ⁻¹' T)).map ((restrictForgetIso U).hom.app F) =
      (restrictForgetIso U).hom.app ((supportedSectionsFunctor X.toRingedSpace T).obj F) ≫
        (restrictAbelian U).map
            ((abelianSupportedSectionsForgetIso X.toRingedSpace T).hom.app F) ≫
          (abelianSupportedSectionsRestrictNatIso (X := X.carrier) T U).hom.app
            ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F) := by
  have h := forget_supportedSectionsRestrict_comm T U F
  simp only [restrictForgetIso, forgetRestrictCompIso, Iso.refl_hom]
  exact h

/-- **The degree-zero module excision read on the homotopy category, before
`DerivedCategory.Qh`.**
`Stacks.Cohomology.SupportedComplexes.supportedSectionsRestrictHomotopyIso`
is this isomorphism whiskered with `DerivedCategory.Qh`; the un-whiskered form is the one at which
the degree-zero square can be proved, every morphism in it being the quotient of a morphism of
cochain complexes. -/
def moduleExcisionHomotopyIso :
    (supportedSectionsOn X T ⋙ Scheme.Modules.restrictFunctor U.ι).mapHomotopyCategory
        (ComplexShape.up ℤ) ≅
      (Scheme.Modules.restrictFunctor U.ι ⋙
        supportedSectionsOn U.toScheme (U.ι ⁻¹' T)).mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (supportedSectionsOn X T ⋙ Scheme.Modules.restrictFunctor U.ι))
      (ComplexShape.up ℤ)).symm ≪≫
    Functor.mapHomotopyCategoryCompIso (supportedSectionsRestrictNatIso T U) (ComplexShape.up ℤ)

/-- **The degree-zero abelian excision read on the homotopy category**, the un-whiskered form of
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictHomotopyIso`. -/
def abelianExcisionHomotopyIso :
    (abelianSupportedSections T ⋙ abelianRestrictOpen (X := X.carrier) U).mapHomotopyCategory
        (ComplexShape.up ℤ) ≅
      (abelianRestrictOpen (X := X.carrier) U ⋙
        abelianSupportedSections (preimageSubset U T)).mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (abelianSupportedSections T ⋙ abelianRestrictOpen (X := X.carrier) U))
      (ComplexShape.up ℤ)).symm ≪≫
    Functor.mapHomotopyCategoryCompIso
      (abelianSupportedSectionsRestrictNatIso (X := X.carrier) T U) (ComplexShape.up ℤ)

/-- The module excision on derived categories is the homotopy-category one localized. -/
theorem supportedSectionsRestrictHomotopyIso_hom_app
    (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (supportedSectionsRestrictHomotopyIso T U).hom.app K =
      DerivedCategory.Qh.map ((moduleExcisionHomotopyIso T U).hom.app K) :=
  rfl

/-- The abelian excision on derived categories is the homotopy-category one localized. -/
theorem abelianSupportedSectionsRestrictHomotopyIso_hom_app
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)) :
    (abelianSupportedSectionsRestrictHomotopyIso (X := X.carrier) T U).hom.app L =
      DerivedCategory.Qh.map ((abelianExcisionHomotopyIso T U).hom.app L) :=
  rfl

/-- **The degree-zero square on the homotopy category of cochain complexes.**  Every morphism in
`forgetExcisionSquare_app` is natural in the module, so each of the four comparisons has a
homotopy-category reading, and the square holds there because it holds in each degree of a
representing complex.  This is the device of
`Stacks.Cohomology.SupportedSectionsForgetPushforward.forgetPushforwardSquare_homotopy`. -/
theorem forgetExcisionHomotopySquare
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (((_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapHomotopyCategory
          (ComplexShape.up ℤ)).map ((moduleExcisionHomotopyIso T U).hom.app K)) ≫
        (forgetCompIso U.toScheme.toRingedSpace (U.ι ⁻¹' T)).hom.app
            (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          ((abelianSupportedSections (U.ι ⁻¹' T)).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((restrictForgetHomotopyIso U).hom.app K) =
      (restrictForgetHomotopyIso U).hom.app
          (((supportedSectionsFunctor X.toRingedSpace T).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        ((restrictAbelian U).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((forgetCompIso X.toRingedSpace T).hom.app K) ≫
          (abelianExcisionHomotopyIso T U).hom.app
            (((_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K) := by
  refine congrArg (HomotopyCategory.quotient
    (Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u})
    (ComplexShape.up ℤ)).map (HomologicalComplex.hom_ext _ _ fun i => ?_)
  exact forgetExcisionSquare_app T U (K.as.X i)

end DegreeZero

/-! ### The composite is a right derived functor -/

section Square

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

/-- The unit exhibiting `R𝓗_T ⋙ (-)|_U^D` as a right derived functor of `H_T(-)|_U`. -/
def restrictUnit :
    (supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH ⋙ (restrictModules U).mapDerivedCategory :=
  Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsFunctor X.toRingedSpace T)
    (restrictModules U) RH aH

/-- **The unit exhibiting `R𝓗_T ⋙ (-)|_U^D ⋙ Φ_U^D` as a right derived functor** of
`H_T(-)|_U` followed by forgetting the module structure: the unit of `R𝓗_T` pushed through the
derived functors of restriction and of forgetting, twice over. -/
def restrictForgetUnit :
    (supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U ⋙
            _root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH ⋙ (restrictModules U).mapDerivedCategory ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory :=
  Stacks.DerivedFunctor.postcomposeUnit
    (supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U)
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))
    (RH ⋙ (restrictModules U).mapDerivedCategory) (restrictUnit T U RH aH)

variable [hRH : RH.IsRightDerivedFunctor aH
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))]

/-- `R𝓗_T ⋙ (-)|_U^D` is a right derived functor of `H_T(-)|_U`: restriction to an open
subscheme is exact. -/
theorem isRightDerivedFunctor_restrict :
    (RH ⋙ (restrictModules U).mapDerivedCategory).IsRightDerivedFunctor (restrictUnit T U RH aH)
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose
    (supportedSectionsFunctor X.toRingedSpace T) (restrictModules U) RH aH
    Stacks.Cohomology.Localization.enoughKInjectives

/-- **`R𝓗_T ⋙ (-)|_U^D ⋙ Φ_U^D` is a right derived functor** of `H_T(-)|_U` followed by
forgetting, with unit `restrictForgetUnit`.  Restriction to an open subscheme and the forgetful
functor are both exact, so this is two applications of
`Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`, and it is what makes the square of
this file a consequence of the degree-zero square: two morphisms out of a right derived functor
agree as soon as they agree after the unit. -/
theorem isRightDerivedFunctor_restrictForget :
    (RH ⋙ (restrictModules U).mapDerivedCategory ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).IsRightDerivedFunctor
      (restrictForgetUnit T U RH aH)
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) :=
  let := isRightDerivedFunctor_restrict T U RH aH
  Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose
    (supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U)
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))
    (RH ⋙ (restrictModules U).mapDerivedCategory) (restrictUnit T U RH aH)
    Stacks.Cohomology.Localization.enoughKInjectives

variable [hRH' : RH'.IsRightDerivedFunctor aH'
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

/-- **The excision side of the square**: derived-category excision for modules, then
[Stacks, Tag 0G74] part (2) on `U`, then the crossing of the two spellings of "restrict and
forget". -/
def excisionThenForget :
    RH ⋙ (restrictModules U).mapDerivedCategory ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ⟶
      (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapDerivedCategory ⋙
        (restrictAbelian U).mapDerivedCategory ⋙ RHab' :=
  Functor.whiskerRight (moduleDerivedExcision T U RH aH RH' aH').hom
      (_root_.SheafOfModules.toSheaf
        (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ≫
    Functor.whiskerLeft (restrictModules U).mapDerivedCategory
      (forgetComparisonOpen T U RH' aH' RHab' aHab') ≫
    Functor.whiskerRight (derivedRestrictCompToSheafIso U).hom RHab'

/-- **The forgetful side of the square**: the crossing, then [Stacks, Tag 0G74] part (2) on `X`,
then derived-category excision for abelian sheaves. -/
def forgetThenExcision :
    RH ⋙ (restrictModules U).mapDerivedCategory ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ⟶
      (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapDerivedCategory ⋙
        (restrictAbelian U).mapDerivedCategory ⋙ RHab' :=
  Functor.whiskerLeft RH (derivedRestrictCompToSheafIso U).hom ≫
    Functor.whiskerRight (forgetComparison T RH aH RHab aHab)
      (restrictAbelian U).mapDerivedCategory ≫
    Functor.whiskerLeft
      (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapDerivedCategory
      (abelianDerivedExcision T U RHab aHab RHab' aHab').hom

/-! ### What pins the four comparisons down -/

/-- The unit exhibiting `(-)|_U^D ⋙ R𝓗_{j⁻¹T}` as a right derived functor of `H_{j⁻¹T}((-)|_U)`,
at the ascribed spellings. -/
def restrictUnit' :
    (restrictModules U ⋙
            supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (restrictModules U).mapDerivedCategory ⋙ RH' :=
  Stacks.DerivedFunctor.precomposeUnit (restrictModules U)
    (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)) RH' aH'

/-- The unit exhibiting `(-)|_U^{ab,D} ⋙ R𝓗^{ab}_{j⁻¹T}` as a right derived functor. -/
def abelianRestrictUnit' :
    (restrictAbelian U ⋙ abelianSupportedSections (U.ι ⁻¹' T)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (restrictAbelian U).mapDerivedCategory ⋙ RHab' :=
  Stacks.DerivedFunctor.precomposeUnit (restrictAbelian U)
    (abelianSupportedSections (U.ι ⁻¹' T)) RHab' aHab'

/-- The unit exhibiting `R𝓗^{ab}_T ⋙ (-)|_U^{ab,D}` as a right derived functor. -/
def abelianRestrictUnit :
    (abelianSupportedSections T ⋙ restrictAbelian U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RHab ⋙ (restrictAbelian U).mapDerivedCategory :=
  Stacks.DerivedFunctor.postcomposeUnit (abelianSupportedSections T) (restrictAbelian U)
    RHab aHab

/-- **The defining factorization of the retyped module excision, at one object.**  This is
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsRestrictNatIso_hom_app` with the
two `CategoryTheory.Functor.IsRightDerivedFunctor` hypotheses handed over explicitly across the
two spellings of the category of modules, exactly as in `moduleDerivedExcision`. -/
theorem moduleDerivedExcision_hom_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (restrictUnit T U RH aH).app K ≫
        (moduleDerivedExcision T U RH aH RH' aH').hom.app (DerivedCategory.Qh.obj K) =
      (supportedSectionsRestrictHomotopyIso T U).hom.app K ≫ (restrictUnit' T U RH' aH').app K :=
  let := qh_isLocalization_schemeModules X
  let := qh_isLocalization_schemeModules U.toScheme
  @derivedSupportedSectionsRestrictNatIso_hom_app _ T U RH aH RH' aH' hRH hRH' K

/-- **The defining factorization of the retyped abelian excision, at one object.** -/
theorem abelianDerivedExcision_hom_app
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :
    (abelianRestrictUnit T U RHab aHab).app L ≫
        (abelianDerivedExcision T U RHab aHab RHab' aHab').hom.app (DerivedCategory.Qh.obj L) =
      (abelianSupportedSectionsRestrictHomotopyIso (X := X.carrier) T U).hom.app L ≫
        (abelianRestrictUnit' T U RHab' aHab').app L :=
  let := qh_isLocalization_openAbelian U
  @derivedAbelianSupportedSectionsRestrictNatIso_hom_app X.toRingedSpace.carrier T U
    RHab aHab RHab' aHab' hRHab hRHab' L

/-- The defining factorization of [Stacks, Tag 0G74] part (2) at one object, over any ringed
space. -/
private theorem abelianSupportedEndoForgetComparison_fac_app_aux (Y : RingedSpace.{u, u})
    (S : Set Y.carrier)
    (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}))
    (aHab : (abelianSupportedSections S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
    (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y)))
    (aH : (supportedSectionsFunctor Y S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ))]
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)) :
    ((_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory).map (aH.app K) ≫
        (abelianSupportedEndoForgetComparison Y S RHab aHab RH aH).app
          (DerivedCategory.Qh.obj K) =
      (abelianSupportedEndoForgetUnit Y S RHab aHab).app K := by
  have h := congr_app (abelianSupportedEndoForgetComparison_fac Y S RHab aHab RH aH) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Stacks.Perfect.SupportedEndoForget.forgetfulSupportedEndoUnit_app] at h
  exact h

omit hRHab in
/-- **The defining factorization of [Stacks, Tag 0G74] part (2) on `X`, at one object.**  The
derivation unit of `R𝓗_T ⋙ Φ_X^D` — which is `Φ_X^D` applied to the unit of `R𝓗_T`, by
`Stacks.Perfect.SupportedEndoForget.forgetfulSupportedEndoUnit_app` — followed by the comparison
is the transported underived comparison. -/
theorem forgetComparison_fac_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapDerivedCategory).map
          (aH.app K) ≫
        (forgetComparison T RH aH RHab aHab).app (DerivedCategory.Qh.obj K) =
      (abelianSupportedEndoForgetUnit X.toRingedSpace T RHab aHab).app K :=
  abelianSupportedEndoForgetComparison_fac_app_aux X.toRingedSpace T RHab aHab RH aH K

omit hRHab' in
/-- **The defining factorization of [Stacks, Tag 0G74] part (2) on `U`, at one object.** -/
theorem forgetComparisonOpen_fac_app
    (L : HomotopyCategory (_root_.SheafOfModules.{u}
      (structureSheafRing U.toScheme.toRingedSpace)) (ComplexShape.up ℤ)) :
    ((_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
          (aH'.app L) ≫
        (forgetComparisonOpen T U RH' aH' RHab' aHab').app (DerivedCategory.Qh.obj L) =
      (abelianSupportedEndoForgetUnit U.toScheme.toRingedSpace (U.ι ⁻¹' T) RHab' aHab').app L :=
  abelianSupportedEndoForgetComparison_fac_app_aux U.toScheme.toRingedSpace (U.ι ⁻¹' T)
    RHab' aHab' RH' aH' L

/-! ### The two sides after the derivation unit -/

/-- **The formal chase on the excision side**, stated at variable categories with every object
implicit and every morphism explicit, and applied with one `exact`.

The five hypotheses are, in order: the outer derivation unit opened by
`Stacks.DerivedFunctor.postcomposeUnit_app`; the defining factorization of the module excision;
the inner unit opened by `Stacks.DerivedFunctor.precomposeUnit_app`; the naturality of
[Stacks, Tag 0G74] part (2) on `U`; and its defining factorization.  At the concrete derived
categories several of the objects in the chain have two definitionally equal spellings, so a
rewrite whose motive mentions them is not type-correct; here there is nothing to unfold. -/
private theorem chaseA {C₁ D₁ : Type*} [Category* C₁] [Category* D₁]
    (F : C₁ ⥤ D₁) (G : D₁ ⥤ D₁) {a a' b c c₀ d d₀ : C₁} {p w : D₁}
    (u0 : p ⟶ F.obj b) (iv : p ⟶ F.obj a) (ru : a ⟶ b) (mm : b ⟶ c)
    (eh : a ⟶ a') (ru' : a' ⟶ c) (ah : a' ⟶ c₀) (rr : c₀ ⟶ c) (ff : d₀ ⟶ d)
    (gg : F.obj c ⟶ G.obj (F.obj d)) (gg₀ : F.obj c₀ ⟶ G.obj (F.obj d₀))
    (aeu : F.obj a' ⟶ G.obj (F.obj d₀)) (tl : G.obj (F.obj d) ⟶ w)
    (h1 : u0 = iv ≫ F.map ru) (h2 : ru ≫ mm = eh ≫ ru') (h3 : ru' = ah ≫ rr)
    (h4 : F.map rr ≫ gg = gg₀ ≫ G.map (F.map ff)) (h5 : F.map ah ≫ gg₀ = aeu) :
    u0 ≫ F.map mm ≫ gg ≫ tl = iv ≫ F.map eh ≫ aeu ≫ G.map (F.map ff) ≫ tl := by
  subst h1 h5 h3
  rw [Category.assoc, ← F.map_comp_assoc, h2, F.map_comp_assoc, F.map_comp_assoc,
    reassoc_of% h4, Category.assoc]

omit hRH in
/-- The outer derivation unit at an object: `Φ_U^D` applied to the unit of `R𝓗_T ⋙ (-)|_U^D`,
after the identification of the two sources.  This is
`Stacks.DerivedFunctor.postcomposeUnit_app`. -/
theorem restrictForgetUnit_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (restrictForgetUnit T U RH aH).app K =
      (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app
          (((supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        ((_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
          ((restrictUnit T U RH aH).app K) :=
  Stacks.DerivedFunctor.postcomposeUnit_app
    (supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U)
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))
    (RH ⋙ (restrictModules U).mapDerivedCategory) (restrictUnit T U RH aH) K

omit hRH' in
/-- The unit of `(-)|_U^D ⋙ R𝓗_{j⁻¹T}` at an object.  This is
`Stacks.DerivedFunctor.precomposeUnit_app`. -/
theorem restrictUnit'_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (restrictUnit' T U RH' aH').app K =
      aH'.app (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        RH'.map ((restrictModules U).mapDerivedCategoryFactorsh.inv.app K) :=
  Stacks.DerivedFunctor.precomposeUnit_app (restrictModules U)
    (supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)) RH' aH' K

omit hRHab' in
/-- **The excision side after the derivation unit.**  One application of `chaseA`: the two
derivation units are opened, the module excision is cancelled against its defining factorization,
and the comparison of [Stacks, Tag 0G74] part (2) on `U` is carried to the image of an object of
the homotopy category by its naturality and cancelled against its own factorization.  What is
left is the degree-zero excision, the transported underived comparison on `U`, and the crossing
of the two spellings. -/
theorem excisionThenForget_unit_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (restrictForgetUnit T U RH aH).app K ≫
        (excisionThenForget T U RH aH RH' aH' RHab' aHab').app (DerivedCategory.Qh.obj K) =
      (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app
          (((supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        ((_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
            ((supportedSectionsRestrictHomotopyIso T U).hom.app K) ≫
          (abelianSupportedEndoForgetUnit U.toScheme.toRingedSpace (U.ι ⁻¹' T) RHab' aHab').app
              (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            RHab'.map (((_root_.SheafOfModules.toSheaf
                (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
                ((restrictModules U).mapDerivedCategoryFactorsh.inv.app K)) ≫
              RHab'.map ((derivedRestrictCompToSheafIso U).hom.app
                (DerivedCategory.Qh.obj K)) := by
  simp only [excisionThenForget, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  exact chaseA _ _ _ _ _ _ _ _
    (aH'.app (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (RH'.map ((restrictModules U).mapDerivedCategoryFactorsh.inv.app K))
    ((restrictModules U).mapDerivedCategoryFactorsh.inv.app K) _ _ _ _
    (restrictForgetUnit_app T U RH aH K)
    (moduleDerivedExcision_hom_app T U RH aH RH' aH' K)
    (restrictUnit'_app T U RH' aH' K)
    ((forgetComparisonOpen T U RH' aH' RHab' aHab').naturality
      ((restrictModules U).mapDerivedCategoryFactorsh.inv.app K))
    (forgetComparisonOpen_fac_app T U RH' aH' RHab' aHab'
      (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))

/-! ### The forgetful side after the derivation unit -/

/-- Rewriting the tail of a composite, at a variable category. -/
private theorem comp_tail_rw {D₀ : Type*} [Category* D₀] {x y z : D₀} (i : x ⟶ y) (f g : y ⟶ z)
    (h : f = g) : i ≫ f = i ≫ g := by rw [h]

/-- A functor image of a four-morphism composite, split.  Stated at variable categories: at the
concrete derived categories the objects along the chain have two spellings each and
`HomologicalComplexUpToQuasiIso.Qh` is not exposed, so a rewrite under the functor's `map` is not
type-correct. -/
private theorem map_four {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (F : C₀ ⥤ D₀)
    {a b c d e : C₀} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) :
    F.map (f ≫ g ≫ h ≫ k) = F.map f ≫ F.map g ≫ F.map h ≫ F.map k := by
  simp only [F.map_comp]

/-- Cancelling an inverse pair at the head of a chain, at a variable category. -/
private theorem cancel_head {D₀ : Type*} [Category* D₀] {x y z : D₀} (i : x ⟶ y) (j : y ⟶ x)
    (f : x ⟶ z) (g : y ⟶ z) (hij : i ≫ j = CategoryStruct.id x) (h : j ≫ f = g) : f = i ≫ g := by
  rw [← h, ← Category.assoc, hij, Category.id_comp]

omit hRH in
/-- The unit of `R𝓗_T ⋙ (-)|_U^D` at an object. -/
theorem restrictUnit_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (restrictUnit T U RH aH).app K =
      (restrictModules U).mapDerivedCategoryFactorsh.inv.app
          (((supportedSectionsFunctor X.toRingedSpace T).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        ((restrictModules U).mapDerivedCategory).map (aH.app K) :=
  Stacks.DerivedFunctor.postcomposeUnit_app (supportedSectionsFunctor X.toRingedSpace T)
    (restrictModules U) RH aH K

omit hRH in
/-- The outer derivation unit at an object, with the inner one opened as well. -/
theorem restrictForgetUnit_app'
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (restrictForgetUnit T U RH aH).app K =
      (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app
          (((supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        ((_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
            ((restrictModules U).mapDerivedCategoryFactorsh.inv.app
              (((supportedSectionsFunctor X.toRingedSpace T).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K)) ≫
          ((_root_.SheafOfModules.toSheaf
                (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
              (((restrictModules U).mapDerivedCategory).map (aH.app K)) := by
  refine (restrictForgetUnit_app T U RH aH K).trans
    (comp_tail_rw _ _ _
      ((congrArg ((_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
        (restrictUnit_app T U RH aH K)).trans (Functor.map_comp _ _ _)))

omit hRHab in
/-- [Stacks, Tag 0G74] part (2) on `X` under the derived functor of abelian restriction. -/
theorem forgetComparison_fac_app'
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    ((restrictAbelian U).mapDerivedCategory).map
          (((_root_.SheafOfModules.toSheaf
            (structureSheafRing X.toRingedSpace)).mapDerivedCategory).map (aH.app K)) ≫
        ((restrictAbelian U).mapDerivedCategory).map
          ((forgetComparison T RH aH RHab aHab).app (DerivedCategory.Qh.obj K)) =
      ((restrictAbelian U).mapDerivedCategory).map
        ((abelianSupportedEndoForgetUnit X.toRingedSpace T RHab aHab).app K) := by
  rw [← Functor.map_comp, forgetComparison_fac_app]

omit hRHab in
/-- The transported underived comparison on `X`, opened and pushed under abelian restriction. -/
theorem abelianSupportedEndoForgetUnit_app_split
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    ((restrictAbelian U).mapDerivedCategory).map
        ((abelianSupportedEndoForgetUnit X.toRingedSpace T RHab aHab).app K) =
      ((restrictAbelian U).mapDerivedCategory).map
          ((_root_.SheafOfModules.toSheaf
                (structureSheafRing X.toRingedSpace)).mapDerivedCategoryFactorsh.hom.app
            (((supportedSectionsFunctor X.toRingedSpace T).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        ((restrictAbelian U).mapDerivedCategory).map
            (DerivedCategory.Qh.map ((forgetCompIso X.toRingedSpace T).hom.app K)) ≫
          ((restrictAbelian U).mapDerivedCategory).map
              (aHab.app (((_root_.SheafOfModules.toSheaf
                (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj K)) ≫
            ((restrictAbelian U).mapDerivedCategory).map
              (RHab.map ((_root_.SheafOfModules.toSheaf
                (structureSheafRing X.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app K)) := by
  exact (congrArg ((restrictAbelian U).mapDerivedCategory).map
      (Stacks.Perfect.SupportedEndoForget.abelianSupportedEndoForgetUnit_app
        X.toRingedSpace T RHab aHab K)).trans
    (map_four _ _ _ _ _)

omit hRHab' in
/-- The unit of `(-)|_U^{ab,D} ⋙ R𝓗^{ab}_{j⁻¹T}` at an object. -/
theorem abelianRestrictUnit'_app
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :
    (abelianRestrictUnit' T U RHab' aHab').app L =
      aHab'.app (((restrictAbelian U).mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
        RHab'.map ((restrictAbelian U).mapDerivedCategoryFactorsh.inv.app L) :=
  Stacks.DerivedFunctor.precomposeUnit_app (restrictAbelian U)
    (abelianSupportedSections (U.ι ⁻¹' T)) RHab' aHab' L

omit hRHab in
/-- The unit of `R𝓗^{ab}_T ⋙ (-)|_U^{ab,D}` at an object. -/
theorem restrictUnitAbelianOpen
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :
    (abelianRestrictUnit T U RHab aHab).app L =
      (restrictAbelian U).mapDerivedCategoryFactorsh.inv.app
          (((abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
        ((restrictAbelian U).mapDerivedCategory).map (aHab.app L) :=
  Stacks.DerivedFunctor.postcomposeUnit_app (abelianSupportedSections T) (restrictAbelian U)
    RHab aHab L

/-- **The abelian excision cancelled against its factorization, with the head moved.**  The
factorization of `abelianDerivedExcision` is stated after the unit of
`R𝓗^{ab}_T ⋙ (-)|_U^{ab,D}`, whose first factor is an isomorphism; moving that factor to the
other side is what lets the excision be used where the chain arrives with the unit of
[Stacks, Tag 0G74] part (2) instead. -/
theorem abelianDerivedExcision_hom_app'
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :
    ((restrictAbelian U).mapDerivedCategory).map (aHab.app L) ≫
        (abelianDerivedExcision T U RHab aHab RHab' aHab').hom.app
          (DerivedCategory.Qh.obj L) =
      (restrictAbelian U).mapDerivedCategoryFactorsh.hom.app
          (((abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
        (abelianSupportedSectionsRestrictHomotopyIso (X := X.carrier) T U).hom.app L ≫
          (abelianRestrictUnit' T U RHab' aHab').app L := by
  refine cancel_head _ _ _ _
    (Iso.hom_inv_id_app (restrictAbelian U).mapDerivedCategoryFactorsh _) ?_
  rw [← Category.assoc, ← restrictUnitAbelianOpen T U RHab aHab L]
  exact abelianDerivedExcision_hom_app T U RHab aHab RHab' aHab' L

/-! ### The crossing, localized -/

/-- Joining three functor images in the tail of a chain. -/
private theorem q_join {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (Q : C₀ ⥤ D₀)
    {a b c d : C₀} {z : D₀} (i : z ⟶ Q.obj a) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    (k : a ⟶ d) (hk : f ≫ g ≫ h = k) :
    i ≫ Q.map f ≫ Q.map g ≫ Q.map h = i ≫ Q.map k := by
  rw [← hk, Q.map_comp, Q.map_comp]

/-- Rewriting the head of a composite, at a variable category. -/
private theorem head_rw {D₀ : Type*} [Category* D₀] {a b c : D₀} (f g : a ⟶ b) (h : b ⟶ c)
    (e : f = g) : f ≫ h = g ≫ h := by rw [e]

/-- Cancelling a round trip at the head of a chain, at a variable category. -/
private theorem cancel_round_trip {D₀ : Type*} [Category* D₀] {o1 o2 o3 o4 : D₀}
    (iv : o1 ⟶ o2) (fmi : o2 ⟶ o3) (fmh : o3 ⟶ o2) (ivh : o2 ⟶ o1) (tail : o1 ⟶ o4)
    (h1 : fmi ≫ fmh = CategoryStruct.id o2) (h2 : iv ≫ ivh = CategoryStruct.id o1) :
    iv ≫ fmi ≫ fmh ≫ ivh ≫ tail = tail := by
  rw [← Category.assoc fmi, h1, Category.id_comp, ← Category.assoc, h2, Category.id_comp]

/-- **The crossing of the two spellings of "restrict and forget", read from the homotopy
category.**  Composing the comparison on derived categories with the two canonical
factorizations on its source is the homotopy-category crossing followed by the two factorizations
on its target.  This is `derivedRestrictCompToSheafIso_hom_app_Qh` with the two inverse pairs it
produces cancelled. -/
theorem crossing_Qh
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app
          (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        ((_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
            ((restrictModules U).mapDerivedCategoryFactorsh.inv.app K) ≫
          (derivedRestrictCompToSheafIso U).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((restrictForgetHomotopyIso U).hom.app K) ≫
        (restrictAbelian U).mapDerivedCategoryFactorsh.inv.app
            (((_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K) ≫
          ((restrictAbelian U).mapDerivedCategory).map
            ((_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app K) := by
  refine Eq.trans (comp_tail_rw _ _ _
    (comp_tail_rw _ _ _ (derivedRestrictCompToSheafIso_hom_app_Qh U K))) ?_
  exact cancel_round_trip _ _ _ _ _
    (Stacks.DerivedIndexing.map_comp_id _ _ _
      (Iso.inv_hom_id_app (restrictModules U).mapDerivedCategoryFactorsh K))
    (Iso.inv_hom_id_app (_root_.SheafOfModules.toSheaf
      (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh _)

/-- The crossing under `R𝓗^{ab}_{j⁻¹T}`. -/
theorem crossing_Qh_under
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    RHab'.map ((_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app
          (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        RHab'.map (((_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
            ((restrictModules U).mapDerivedCategoryFactorsh.inv.app K)) ≫
          RHab'.map ((derivedRestrictCompToSheafIso U).hom.app (DerivedCategory.Qh.obj K)) =
      RHab'.map (DerivedCategory.Qh.map ((restrictForgetHomotopyIso U).hom.app K)) ≫
        RHab'.map ((restrictAbelian U).mapDerivedCategoryFactorsh.inv.app
            (((_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K)) ≫
          RHab'.map (((restrictAbelian U).mapDerivedCategory).map
            ((_root_.SheafOfModules.toSheaf
              (structureSheafRing X.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app K)) :=
  ((RHab'.map_comp₃ _ _ _).symm.trans
    (congrArg RHab'.map (crossing_Qh U K))).trans (RHab'.map_comp₃ _ _ _)

/-- **The assembly of the localized degree-zero square**, at variable categories with every
object implicit: the naturality of the canonical factorization moves it across the degree-zero
excision, and what is left is the homotopy-category square under `DerivedCategory.Qh`. -/
private theorem star2_chase {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (Q : C₀ ⥤ D₀)
    {y y' : D₀} {a b c d e f : C₀}
    (feh : y ⟶ y') (fhomU : y' ⟶ Q.obj b) (fhom : y ⟶ Q.obj a)
    (psi : a ⟶ b) (f1 : b ⟶ c) (f2 : c ⟶ d)
    (g1 : a ⟶ e) (g2 : e ⟶ f) (g3 : f ⟶ d)
    (hnat : feh ≫ fhomU = fhom ≫ Q.map psi)
    (hsq : psi ≫ f1 ≫ f2 = g1 ≫ g2 ≫ g3) :
    feh ≫ fhomU ≫ Q.map f1 ≫ Q.map f2 = fhom ≫ Q.map g1 ≫ Q.map g2 ≫ Q.map g3 := by
  rw [reassoc_of% hnat, ← Q.map_comp, ← Q.map_comp, ← Q.map_comp, hsq, Q.map_comp,
    Q.map_comp]

/-- **The degree-zero square, localized.**  The homotopy-category square
`forgetExcisionHomotopySquare` read through `DerivedCategory.Qh`, with the canonical factorization
of the forgetful functor on `U` moved across the degree-zero excision by its own naturality. -/
theorem forgetExcisionQhSquare
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    ((_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
          ((supportedSectionsRestrictHomotopyIso T U).hom.app K) ≫
        (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.hom.app
            (((supportedSectionsFunctor U.toScheme.toRingedSpace
              (U.ι ⁻¹' T)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
                (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
          DerivedCategory.Qh.map ((forgetCompIso U.toScheme.toRingedSpace
              (U.ι ⁻¹' T)).hom.app
              (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
            DerivedCategory.Qh.map (((abelianSupportedSections (U.ι ⁻¹' T)).mapHomotopyCategory
              (ComplexShape.up ℤ)).map ((restrictForgetHomotopyIso U).hom.app K)) =
      (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((restrictForgetHomotopyIso U).hom.app
            (((supportedSectionsFunctor X.toRingedSpace T).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
          DerivedCategory.Qh.map (((restrictAbelian U).mapHomotopyCategory
              (ComplexShape.up ℤ)).map ((forgetCompIso X.toRingedSpace T).hom.app K)) ≫
            (abelianSupportedSectionsRestrictHomotopyIso (X := X.carrier) T U).hom.app
              (((_root_.SheafOfModules.toSheaf
                (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj K) := by
  have hnat := (_root_.SheafOfModules.toSheaf
      (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.hom.naturality
    ((moduleExcisionHomotopyIso T U).hom.app K)
  exact star2_chase DerivedCategory.Qh _ _ _ _ _ _ _ _ _ hnat
    (forgetExcisionHomotopySquare T U K)

/-! ### The square -/

/-- **The formal chase on the forgetful side**, stated at a variable category with every object
implicit and every morphism explicit, and applied with one `exact`.

The sixteen hypotheses are, in order: the derivation unit opened twice; the naturality of the
crossing; the defining factorization of [Stacks, Tag 0G74] part (2) on `X` under abelian
restriction; the transported underived comparison on `X` split into its four factors; the
naturality of the abelian excision; its defining factorization with the head moved; the unit of
`(-)|_U^{ab,D} ⋙ R𝓗^{ab}_{j⁻¹T}` opened; the crossing localized, at the supported-sections
complex; two inverse pairs and the naturality of the canonical factorization of abelian
restriction, which together carry the crossing past the comparison on `X`; the localized
degree-zero square; the remaining inverse pair; the naturality of the derivation unit of
`R𝓗^{ab}_{j⁻¹T}`; the transported underived comparison on `U`; and the crossing localized under
`R𝓗^{ab}_{j⁻¹T}`. -/
private theorem chaseB {D₀ : Type*} [Category* D₀]
    {o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o14 o15 o16 o18
      o19 o20 o21 o23 o24 o25 : D₀}
    (u0 : o1 ⟶ o4) (iv : o1 ⟶ o2) (fr1 : o2 ⟶ o3) (fjm : o3 ⟶ o4)
    (cq : o4 ⟶ o5) (rg : o5 ⟶ o6) (mq : o6 ⟶ o7)
    (cq0 : o3 ⟶ o8) (rjx : o8 ⟶ o5) (raeu : o8 ⟶ o6)
    (rp1 : o8 ⟶ o9) (rp2 : o9 ⟶ o10) (rab : o10 ⟶ o11) (rz2 : o11 ⟶ o6)
    (mq0 : o11 ⟶ o12) (gh2 : o12 ⟶ o7)
    (rafh : o10 ⟶ o18) (ehb : o18 ⟶ o14) (u2 : o14 ⟶ o12)
    (ab' : o14 ⟶ o15) (grai : o15 ⟶ o12)
    (qr : o1 ⟶ o16) (rai : o16 ⟶ o9) (rax : o9 ⟶ o8)
    (qrafcx : o16 ⟶ o18) (rainvm : o18 ⟶ o10)
    (feh : o2 ⟶ o19) (aeu : o19 ⟶ o24) (gff : o24 ⟶ o25) (tl : o25 ⟶ o7)
    (fhomU : o19 ⟶ o20) (qfcU : o20 ⟶ o21) (abU : o21 ⟶ o23) (gphuinv : o23 ⟶ o24)
    (qaphi : o21 ⟶ o14) (fhom : o2 ⟶ o1) (gqphi : o23 ⟶ o15)
    (h0 : u0 = iv ≫ fr1 ≫ fjm) (h2 : fjm ≫ cq = cq0 ≫ rjx) (h3 : rjx ≫ rg = raeu)
    (h4 : raeu = rp1 ≫ rp2 ≫ rab ≫ rz2) (h5 : rz2 ≫ mq = mq0 ≫ gh2)
    (h6 : rab ≫ mq0 = rafh ≫ ehb ≫ u2) (h7 : u2 = ab' ≫ grai)
    (h8 : iv ≫ fr1 ≫ cq0 = qr ≫ rai ≫ rax) (h9 : rax ≫ rp1 = CategoryStruct.id o9)
    (h10 : rai ≫ rp2 = qrafcx ≫ rainvm) (h11 : rainvm ≫ rafh = CategoryStruct.id o18)
    (h12 : feh ≫ fhomU ≫ qfcU ≫ qaphi = fhom ≫ qr ≫ qrafcx ≫ ehb)
    (h13 : iv ≫ fhom = CategoryStruct.id o1) (h14 : qaphi ≫ ab' = abU ≫ gqphi)
    (h15 : aeu = fhomU ≫ qfcU ≫ abU ≫ gphuinv)
    (h16 : gphuinv ≫ gff ≫ tl = gqphi ≫ grai ≫ gh2) :
    u0 ≫ cq ≫ rg ≫ mq = iv ≫ feh ≫ aeu ≫ gff ≫ tl := by
  calc u0 ≫ cq ≫ rg ≫ mq
      = iv ≫ fr1 ≫ (fjm ≫ cq) ≫ rg ≫ mq := by rw [h0]; simp only [Category.assoc]
    _ = iv ≫ fr1 ≫ cq0 ≫ (rjx ≫ rg) ≫ mq := by rw [h2]; simp only [Category.assoc]
    _ = iv ≫ fr1 ≫ cq0 ≫ raeu ≫ mq := by rw [h3]
    _ = iv ≫ fr1 ≫ cq0 ≫ rp1 ≫ rp2 ≫ rab ≫ (rz2 ≫ mq) := by
        rw [h4]; simp only [Category.assoc]
    _ = iv ≫ fr1 ≫ cq0 ≫ rp1 ≫ rp2 ≫ (rab ≫ mq0) ≫ gh2 := by
        rw [h5]; simp only [Category.assoc]
    _ = iv ≫ fr1 ≫ cq0 ≫ rp1 ≫ rp2 ≫ rafh ≫ ehb ≫ u2 ≫ gh2 := by
        rw [h6]; simp only [Category.assoc]
    _ = (iv ≫ fr1 ≫ cq0) ≫ rp1 ≫ rp2 ≫ rafh ≫ ehb ≫ ab' ≫ grai ≫ gh2 := by
        rw [h7]; simp only [Category.assoc]
    _ = qr ≫ rai ≫ (rax ≫ rp1) ≫ rp2 ≫ rafh ≫ ehb ≫ ab' ≫ grai ≫ gh2 := by
        rw [h8]; simp only [Category.assoc]
    _ = qr ≫ (rai ≫ rp2) ≫ rafh ≫ ehb ≫ ab' ≫ grai ≫ gh2 := by
        rw [h9, Category.id_comp]; simp only [Category.assoc]
    _ = qr ≫ qrafcx ≫ (rainvm ≫ rafh) ≫ ehb ≫ ab' ≫ grai ≫ gh2 := by
        rw [h10]; simp only [Category.assoc]
    _ = qr ≫ qrafcx ≫ ehb ≫ ab' ≫ grai ≫ gh2 := by
        rw [h11, Category.id_comp]
    _ = (iv ≫ fhom) ≫ qr ≫ qrafcx ≫ ehb ≫ ab' ≫ grai ≫ gh2 := by
        rw [h13, Category.id_comp]
    _ = iv ≫ (fhom ≫ qr ≫ qrafcx ≫ ehb) ≫ ab' ≫ grai ≫ gh2 := by
        simp only [Category.assoc]
    _ = iv ≫ (feh ≫ fhomU ≫ qfcU ≫ qaphi) ≫ ab' ≫ grai ≫ gh2 := by rw [h12]
    _ = iv ≫ feh ≫ fhomU ≫ qfcU ≫ (qaphi ≫ ab') ≫ grai ≫ gh2 := by
        simp only [Category.assoc]
    _ = iv ≫ feh ≫ fhomU ≫ qfcU ≫ abU ≫ (gqphi ≫ grai ≫ gh2) := by
        rw [h14]; simp only [Category.assoc]
    _ = iv ≫ feh ≫ fhomU ≫ qfcU ≫ abU ≫ gphuinv ≫ gff ≫ tl := by rw [← h16]
    _ = iv ≫ feh ≫ (fhomU ≫ qfcU ≫ abU ≫ gphuinv) ≫ gff ≫ tl := by
        simp only [Category.assoc]
    _ = iv ≫ feh ≫ aeu ≫ gff ≫ tl := by rw [← h15]

/-- **The forgetful side after the derivation unit** reduces to exactly what the excision side
reduces to, by `chaseB`. -/
theorem forgetThenExcision_unit_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (restrictForgetUnit T U RH aH).app K ≫
        (forgetThenExcision T U RH aH RHab aHab RHab' aHab').app (DerivedCategory.Qh.obj K) =
      (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app
          (((supportedSectionsFunctor X.toRingedSpace T ⋙ restrictModules U).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        ((_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
            ((supportedSectionsRestrictHomotopyIso T U).hom.app K) ≫
          (abelianSupportedEndoForgetUnit U.toScheme.toRingedSpace (U.ι ⁻¹' T) RHab' aHab').app
              (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            RHab'.map (((_root_.SheafOfModules.toSheaf
                (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).map
                ((restrictModules U).mapDerivedCategoryFactorsh.inv.app K)) ≫
              RHab'.map ((derivedRestrictCompToSheafIso U).hom.app
                (DerivedCategory.Qh.obj K)) := by
  simp only [forgetThenExcision, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  exact chaseB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (restrictForgetUnit_app' T U RH aH K)
    ((derivedRestrictCompToSheafIso U).hom.naturality (aH.app K))
    (forgetComparison_fac_app' T U RH aH RHab aHab K)
    (abelianSupportedEndoForgetUnit_app_split T U RHab aHab K)
    ((abelianDerivedExcision T U RHab aHab RHab' aHab').hom.naturality
      ((_root_.SheafOfModules.toSheaf
        (structureSheafRing X.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app K))
    (abelianDerivedExcision_hom_app' T U RHab aHab RHab' aHab'
      (((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K))
    (abelianRestrictUnit'_app T U RHab' aHab'
      (((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K))
    (crossing_Qh U (((supportedSectionsFunctor X.toRingedSpace T).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj K))
    (Stacks.DerivedIndexing.map_comp_id ((restrictAbelian U).mapDerivedCategory) _ _
      (Iso.inv_hom_id_app (_root_.SheafOfModules.toSheaf
        (structureSheafRing X.toRingedSpace)).mapDerivedCategoryFactorsh _))
    (((restrictAbelian U).mapDerivedCategoryFactorsh.inv.naturality
      ((forgetCompIso X.toRingedSpace T).hom.app K)).symm)
    (Iso.inv_hom_id_app (restrictAbelian U).mapDerivedCategoryFactorsh _)
    (forgetExcisionQhSquare T U K)
    (Iso.inv_hom_id_app (_root_.SheafOfModules.toSheaf
      (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh _)
    (aHab'.naturality ((restrictForgetHomotopyIso U).hom.app K))
    (Stacks.Perfect.SupportedEndoForget.abelianSupportedEndoForgetUnit_app
      U.toScheme.toRingedSpace (U.ι ⁻¹' T) RHab' aHab'
      (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (crossing_Qh_under U RHab' K)

/-- **[Stacks, Tag 0G74] part (2) commutes with both excisions, on the unbounded derived
category.**  For a scheme `X`, a subset `T ⊆ X`, an open subscheme `U ⊆ X` and arbitrary total
right derived functors of the four supported-sections functors with their derivation units, the
square formed by

* derived-category excision for the local cohomology of sheaves of modules,
* [Stacks, Tag 0G74] part (2) on `U`,
* [Stacks, Tag 0G74] part (2) on `X`, and
* derived-category excision for abelian local cohomology,

read through the comparison
`Stacks.Cohomology.RestrictForgetComparison.derivedRestrictCompToSheafIso` of the two spellings
of "restrict and forget", commutes.

The source `R𝓗_T ⋙ (-)|_U^D ⋙ Φ_U^D` is a right derived functor of `H_T(-)|_U` followed by
forgetting — restriction to an open subscheme and the forgetful functor are both exact — so by
`CategoryTheory.Functor.rightDerived_ext` the two sides agree as soon as they agree after the
derivation unit, and there each of the four comparisons is cancelled against its own defining
factorization.  What is left is the degree-zero square
`Stacks.Cohomology.SupportedComplexes.forget_supportedSectionsRestrict_comm`, read on the
homotopy category of cochain complexes and then localized. -/
theorem forgetExcisionDerivedSquare :
    excisionThenForget T U RH aH RH' aH' RHab' aHab' =
      forgetThenExcision T U RH aH RHab aHab RHab' aHab' := by
  have := isRightDerivedFunctor_restrictForget T U RH aH
  refine Functor.rightDerived_ext _ (restrictForgetUnit T U RH aH)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  exact (excisionThenForget_unit_app T U RH aH RH' aH' RHab' aHab' K).trans
    (forgetThenExcision_unit_app T U RH aH RHab aHab RHab' aHab' K).symm

end Square

end Stacks.Cohomology.DerivedExcisionSquare

end
