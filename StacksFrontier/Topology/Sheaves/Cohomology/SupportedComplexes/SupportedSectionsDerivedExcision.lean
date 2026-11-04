module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPostcomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPrecomposeExact
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcision
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived-category excision for the local cohomology of sheaves of modules

Let `X` be a scheme, let `T ⊆ X` be a subset and let `U ⊆ X` be an open subscheme with inclusion
`j : U → X`.  On the **unbounded** derived category of sheaves of `𝒪_X`-modules a total right
derived functor `RH_T` of the subsheaf of sections supported on `T` commutes with restriction to
`U`:

`RH_T(K)|_U ≅ RH_{j⁻¹T}(K|_U)`,

naturally in `K : D(Mod(𝒪_X))`.  That is `derivedSupportedSectionsRestrictNatIso`, stated for an
*arbitrary* pair of total right derived functors with their units, so that it composes with the
statements that quantify over theirs.

This is the module analogue of
`Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsRestrictNatIso`: the same
comparison with "sheaves of abelian groups on a topological space" replaced throughout by "sheaves
of modules on a scheme".  The degree-zero excision it is built from is
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`, and the classical
`ℕ`-indexed comparison it refines is
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`; neither of those is a
statement about the unbounded derived category, and that is what is supplied here.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.derivedSupportedSections`: **`RH_T` on sheaves of modules
  for an arbitrary subset `T` of a scheme**, the total right derived functor of the subsheaf of
  sections supported on `T`, with
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsUnit` its derivation unit and
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSections_isRightDerivedFunctor` the
  instance saying so.  It is built by the `CategoryTheory.Functor.totalRightDerived` recipe and it
  instantiates everything below.
* `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsCompRestrictUnit` and
  `Stacks.Cohomology.SupportedComplexes.derivedRestrictCompSupportedSectionsUnit`: the units
  exhibiting the two composites as right derived functors of `H_T(-)|_U` and of
  `H_{j⁻¹T}((-)|_U)`.
* `Stacks.Cohomology.SupportedComplexes.moduleExtendByZero` and
  `Stacks.Cohomology.SupportedComplexes.moduleExtendByZeroAdjunction`: extension by zero of
  sheaves of modules along the inclusion of an open subscheme and its adjunction with restriction,
  both at the `AlgebraicGeometry.Scheme.Modules` spelling of the two categories.
* `Stacks.Cohomology.SupportedComplexes.supportedSectionsRestrictHomotopyIso`: the degree-zero
  excision read on the homotopy category and then on the derived category, which is the single
  mathematical input of the comparison.

## Main results

* `Stacks.Cohomology.SupportedComplexes.isRightDerivedFunctor_derivedSupportedSectionsComp`:
  `RH_T ⋙ (-)|_U` **is** a right derived functor of `H_T(-)|_U`, restriction of modules to an open
  subscheme being exact.
* `Stacks.Cohomology.SupportedComplexes.isRightDerivedFunctor_restrictCompSupportedSections`:
  `(-)|_U ⋙ RH_{j⁻¹T}` **is** a right derived functor of `H_{j⁻¹T}((-)|_U)`, restriction having
  the exact left adjoint "extension by zero" and hence preserving K-injectivity
  ([Stacks, Tag 08BJ]).
* `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsRestrictNatIso`:
  **derived-category excision for the local cohomology of sheaves of modules**,
  `RH_T ⋙ (-)|_U ≅ (-)|_U ⋙ RH_{j⁻¹T}`.  No closedness assumption on `T` is needed.
* `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsRestrictNatIso_fac` and
  `..._hom_app`: **the defining factorization**, in natural-transformation and in componentwise
  form — the unit of the first composite followed by the comparison is the degreewise excision
  followed by the unit of the second.  This is the `CategoryTheory.Functor.rightDerived_fac`
  specialisation a consumer computing the comparison after a derivation unit uses, and it is the
  one property that pins the comparison down.

## Implementation notes

**The route.**  Both composites are right derived functors of degreewise-isomorphic functors, so
Mathlib's `CategoryTheory.Functor.rightDerivedNatIso` supplies the comparison.  The two
presuppositions are discharged by the two generic statements of the project rather than rebuilt:

* post-composition, `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`, which needs only
  that restriction of modules to an open subscheme is exact
  (`Stacks.Perfect.LocalCohomologyExcision.restrictFunctor_preservesFiniteColimits` and
  `...restrictFunctor_preservesHomology`); it is a consequence of absoluteness of a right derived
  functor computed by K-injective resolutions;
* pre-composition, `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint`,
  which is *not* formal: it asks that restriction carry K-injective complexes to K-injective ones,
  and that holds by [Stacks, Tag 08BJ] because `moduleExtendByZeroAdjunction` exhibits restriction
  as the right adjoint of extension by zero, which is exact.

The K-injective-resolution hypotheses of both are
`Stacks.Cohomology.Localization.enoughKInjectives`, sheaves of modules on a scheme being
Grothendieck abelian.  The degreewise input is
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`, which is where the
mathematics is; everything above it is the uniqueness of right derived functors.

**Exactness of extension by zero of modules is not reproved here.**  It is
`ExtensionByZeroModules.jShriek_preservesFiniteLimits` and
`ExtensionByZeroModules.jShriek_preservesColimitsOfSize`, where the substance — that `j_!`
preserves monomorphisms, read on stalks — is carried out.  All that is added here is the spelling.

**Two names for one category, again.**  `AlgebraicGeometry.Scheme.Modules` is a `def` with its own
`Category` instance, so `X.Modules` and `SheafOfModules (structureSheafRing X.toRingedSpace)` are
definitionally equal but are different instance-search keys; the implementation notes of
`Stacks.Perfect.LocalCohomologyExcision` record this, and it is why `supportedSectionsOn` exists at
all.  The same hazard applies to the *left adjoint* of restriction:
`ExtensionByZeroModules.jShriek` is stated at the `SheafOfModules` spelling, and its `Additive`,
`PreservesFiniteLimits` and `PreservesFiniteColimits` instances are not found at an application
whose categories are written `U.toScheme.Modules` and `X.Modules`.  The remedy is
`moduleExtendByZero`, an abbreviation for `jShriek` with its source and target *ascribed* at the
`Scheme.Modules` spelling, carrying the three instances at that spelling, together with
`moduleExtendByZeroAdjunction`, which is `ExtensionByZeroModules.jShriekAdjunction` retyped there
through `Stacks.Perfect.LocalCohomologyExcision.restrictFunctor_eq_jStar`.  That equality of
functors — not merely an isomorphism — is what lets the adjunction be transported by rewriting.

**No `@[stacks ...]` attribute is attached to any declaration here.**  Excision for local
cohomology is not a numbered result of the source, exactly as in
`Stacks.Perfect.LocalCohomologyExcision`; the generic homological algebra used is tagged where it
is proved.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Perfect.LocalCohomologyExcision

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

attribute [local instance] HasDerivedCategory.standard

/-! ### Existence of the total right derived functor -/

/-- **Every functor out of the homotopy category of sheaves of modules on a scheme has a total
right derived functor.**  Sheaves of modules on a scheme are Grothendieck abelian, so every
cochain complex of them admits a quasi-isomorphism into a K-injective one and
`Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck` applies. -/
theorem hasRightDerivedFunctor_schemeModules {X : Scheme.{u}} {H : Type*} [Category* H]
    (F : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck _ F

/-! ### `RH_T` on sheaves of modules -/

/-- **`RH_T` on sheaves of modules**, the total right derived functor of the subsheaf of sections
supported on the subset `T` of the scheme `X`, along the localization of the homotopy category at
the quasi-isomorphisms.

No closedness of `T` is needed.  The `HasRightDerivedFunctor` hypothesis of
`CategoryTheory.Functor.totalRightDerived` is supplied from
`hasRightDerivedFunctor_schemeModules`. -/
@[sga "4 V 6.3" "special case"]
def derivedSupportedSections (X : Scheme.{u}) (T : Set X) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  let := hasRightDerivedFunctor_schemeModules
    ((supportedSectionsOn X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  Functor.totalRightDerived
    ((supportedSectionsOn X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The derivation unit of `derivedSupportedSections`: the canonical comparison from the subsheaf
of sections of a complex of `𝒪_X`-modules supported on `T` to the value of the total right derived
functor on it, with the `HasRightDerivedFunctor` hypothesis supplied exactly as in the functor
itself. -/
def derivedSupportedSectionsUnit (X : Scheme.{u}) (T : Set X) :
    (supportedSectionsOn X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSupportedSections X T :=
  let := hasRightDerivedFunctor_schemeModules
    ((supportedSectionsOn X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  Functor.totalRightDerivedUnit
    ((supportedSectionsOn X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- **The unit exhibits `derivedSupportedSections` as the right derived functor of the subsheaf of
supported sections.**  Both it and its unit are the `totalRightDerived` data of the same functor,
so the general instance applies after unfolding; the `HasRightDerivedFunctor` hypothesis is a
`Prop` and is supplied the same way in both. -/
instance derivedSupportedSections_isRightDerivedFunctor (X : Scheme.{u}) (T : Set X) :
    (derivedSupportedSections X T).IsRightDerivedFunctor (derivedSupportedSectionsUnit X T)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  dsimp only [derivedSupportedSections, derivedSupportedSectionsUnit]
  infer_instance

/-! ### Exactness and additivity of extension by zero -/

section Adjunction

variable {X : Scheme.{u}} (U : X.Opens)

/-- **Extension by zero of sheaves of modules along the inclusion of an open subscheme**, with its
source and target spelled as the modules on the open subscheme and on the ambient scheme.  This is
`ExtensionByZeroModules.jShriek` of [Stacks, Tag 00AB]; only the spelling of the two categories
differs, and the spelling is what matters, for the reason recorded in the module docstring:
`U.toScheme.Modules` and `SheafOfModules (ExtensionByZeroModules.resRing U _)` are definitionally
equal but are different instance-search keys, and the left adjoint of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι` has to be presented at the former for the
instances below to be the ones an application needs. -/
@[sga "4 XVII 5.1.1"]
abbrev moduleExtendByZero : U.toScheme.Modules ⥤ X.Modules :=
  ExtensionByZeroModules.jShriek (X := X.toRingedSpace.carrier) U
    (structureSheafRing X.toRingedSpace)

/-- **Extension by zero of modules is left exact**, at the spelling of `moduleExtendByZero`.  It
is additive and preserves monomorphisms and cokernels, which is
`ExtensionByZeroModules.jShriek_preservesFiniteLimits`. -/
instance moduleExtendByZero_preservesFiniteLimits :
    PreservesFiniteLimits (moduleExtendByZero U) :=
  inferInstanceAs (PreservesFiniteLimits
    (ExtensionByZeroModules.jShriek (X := X.toRingedSpace.carrier) U
      (structureSheafRing X.toRingedSpace)))

/-- **Extension by zero of modules is right exact**, at the spelling of `moduleExtendByZero`: it
is a left adjoint, so it preserves all colimits. -/
instance moduleExtendByZero_preservesFiniteColimits :
    PreservesFiniteColimits (moduleExtendByZero U) :=
  inferInstanceAs (PreservesFiniteColimits
    (ExtensionByZeroModules.jShriek (X := X.toRingedSpace.carrier) U
      (structureSheafRing X.toRingedSpace)))

/-- Extension by zero of modules is additive, being the left adjoint of the additive restriction
functor. -/
instance moduleExtendByZero_additive : (moduleExtendByZero U).Additive :=
  inferInstanceAs (ExtensionByZeroModules.jShriek (X := X.toRingedSpace.carrier) U
    (structureSheafRing X.toRingedSpace)).Additive

/-- **Extension by zero is left adjoint to restriction to an open subscheme**, at the two ascribed
spellings.  This is `ExtensionByZeroModules.jShriekAdjunction` retyped: restriction of modules to
an open subscheme *is* the restriction `j^*` of extension by zero, by
`Stacks.Perfect.LocalCohomologyExcision.restrictFunctor_eq_jStar`, and that is an equality of
functors, so the adjunction transports by rewriting. -/
def moduleExtendByZeroAdjunction :
    moduleExtendByZero U ⊣ Scheme.Modules.restrictFunctor U.ι := by
  rw [restrictFunctor_eq_jStar]
  exact ExtensionByZeroModules.jShriekAdjunction (X := X.toRingedSpace.carrier) U
    (structureSheafRing X.toRingedSpace)

end Adjunction

/-! ### The two units and the degreewise comparison -/

section Derived

variable {X : Scheme.{u}} (T : Set X) (U : X.Opens)
  (RH : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules)
  (aH : (supportedSectionsOn X T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
  (RH' : DerivedCategory U.toScheme.Modules ⥤ DerivedCategory U.toScheme.Modules)
  (aH' : (supportedSectionsOn U.toScheme (U.ι ⁻¹' T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH')

/-- The unit exhibiting `RH_T ⋙ (-)|_U` as a right derived functor of `H_T(-)|_U`: the unit `aH`
of `RH_T` pushed through the derived functor of restriction, after the identification of the two
sources.  This is `Stacks.DerivedFunctor.postcomposeUnit` at the data of this file, and
`Stacks.DerivedFunctor.postcomposeUnit_app` computes it at an object. -/
def derivedSupportedSectionsCompRestrictUnit :
    (supportedSectionsOn X T ⋙ Scheme.Modules.restrictFunctor U.ι).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH ⋙ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
  Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOn X T)
    (Scheme.Modules.restrictFunctor U.ι) RH aH

/-- The unit exhibiting `(-)|_U ⋙ RH_{j⁻¹T}` as a right derived functor of `H_{j⁻¹T}((-)|_U)`:
the unit `aH'` of `RH_{j⁻¹T}` at the restriction of a complex, between the two reassociations.
This is `Stacks.DerivedFunctor.precomposeUnit` at the data of this file, and
`Stacks.DerivedFunctor.precomposeUnit_app` computes it at an object. -/
def derivedRestrictCompSupportedSectionsUnit :
    (Scheme.Modules.restrictFunctor U.ι ⋙
            supportedSectionsOn U.toScheme (U.ι ⁻¹' T)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⋙ RH' :=
  Stacks.DerivedFunctor.precomposeUnit (Scheme.Modules.restrictFunctor U.ι)
    (supportedSectionsOn U.toScheme (U.ι ⁻¹' T)) RH' aH'

/-- **The degree-zero excision, read on the homotopy category and then on the derived category.**
This is `Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso` applied
degreewise: the comparison of the homotopy-category functor of a composite with the composite of
the homotopy-category functors, inverted, then the degree-zero excision, then
`DerivedCategory.Qh`.  It is the single mathematical input of
`derivedSupportedSectionsRestrictNatIso`. -/
def supportedSectionsRestrictHomotopyIso :
    (supportedSectionsOn X T ⋙ Scheme.Modules.restrictFunctor U.ι).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (Scheme.Modules.restrictFunctor U.ι ⋙
            supportedSectionsOn U.toScheme (U.ι ⁻¹' T)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.isoWhiskerRight
    ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (supportedSectionsOn X T ⋙ Scheme.Modules.restrictFunctor U.ι))
          (ComplexShape.up ℤ)).symm ≪≫
      Functor.mapHomotopyCategoryCompIso (supportedSectionsRestrictNatIso T U)
        (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- **`RH_T ⋙ (-)|_U` is a right derived functor of `H_T(-)|_U`.**  Restriction of modules to an
open subscheme is exact, so this is absoluteness of a right derived functor computed by
K-injective resolutions, `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`; the existence
of those resolutions is `Stacks.Cohomology.Localization.enoughKInjectives`. -/
theorem isRightDerivedFunctor_derivedSupportedSectionsComp
    [RH.IsRightDerivedFunctor aH (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    (RH ⋙ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory).IsRightDerivedFunctor
      (derivedSupportedSectionsCompRestrictUnit T U RH aH)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose (supportedSectionsOn X T)
    (Scheme.Modules.restrictFunctor U.ι) RH aH
    Stacks.Cohomology.Localization.enoughKInjectives

/-- **`(-)|_U ⋙ RH_{j⁻¹T}` is a right derived functor of `H_{j⁻¹T}((-)|_U)`.**  Unlike the
post-composition statement this is not formal: it needs that restriction to an open subscheme
carries K-injective complexes to K-injective ones, which holds by [Stacks, Tag 08BJ] because
`moduleExtendByZeroAdjunction` exhibits restriction as the right adjoint of extension by zero, and
extension by zero of modules is exact. -/
theorem isRightDerivedFunctor_restrictCompSupportedSections
    [RH'.IsRightDerivedFunctor aH'
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))] :
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⋙ RH').IsRightDerivedFunctor
      (derivedRestrictCompSupportedSectionsUnit T U RH' aH')
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint
    (Scheme.Modules.restrictFunctor U.ι) (supportedSectionsOn U.toScheme (U.ι ⁻¹' T)) RH' aH'
    (moduleExtendByZero U) (moduleExtendByZeroAdjunction U)
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives

/-- **Derived-category excision for the local cohomology of sheaves of modules.**  For a scheme
`X`, a subset `T ⊆ X` and an open subscheme `U ⊆ X` with inclusion `j : U → X`,

`RH_T(K)|_U ≅ RH_{j⁻¹T}(K|_U)`,

naturally in `K` in the unbounded derived category of `𝒪_X`-modules, for any total right derived
functors `RH_T` of `H_T` and `RH_{j⁻¹T}` of `H_{j⁻¹T}` with units `aH` and `aH'`.  No closedness
assumption on `T` is needed.

Both sides are right derived functors of the degreewise-isomorphic functors `H_T(-)|_U` and
`H_{j⁻¹T}((-)|_U)` — the two theorems above — so the uniqueness of right derived functors,
`CategoryTheory.Functor.rightDerivedNatIso`, supplies the comparison from the degree-zero excision
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`.  What pins it down is
`derivedSupportedSectionsRestrictNatIso_fac`. -/
@[sga "4 V 6.4" "Clause 1), special case"]
def derivedSupportedSectionsRestrictNatIso
    [RH.IsRightDerivedFunctor aH (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [RH'.IsRightDerivedFunctor aH'
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))] :
    RH ⋙ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⋙ RH' :=
  have := isRightDerivedFunctor_derivedSupportedSectionsComp T U RH aH
  have := isRightDerivedFunctor_restrictCompSupportedSections T U RH' aH'
  Functor.rightDerivedNatIso (RH ⋙ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory)
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⋙ RH')
    (derivedSupportedSectionsCompRestrictUnit T U RH aH)
    (derivedRestrictCompSupportedSectionsUnit T U RH' aH')
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (supportedSectionsRestrictHomotopyIso T U)

/-- **The defining factorization of the derived excision.**  The unit exhibiting `RH_T ⋙ (-)|_U`
as a right derived functor, followed by the comparison, is the degreewise excision followed by the
unit exhibiting `(-)|_U ⋙ RH_{j⁻¹T}` as one.  This is the
`CategoryTheory.Functor.rightDerived_fac` factorization at the data of this file, and it is the
one property that determines `derivedSupportedSectionsRestrictNatIso`. -/
theorem derivedSupportedSectionsRestrictNatIso_fac
    [RH.IsRightDerivedFunctor aH (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [RH'.IsRightDerivedFunctor aH'
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))] :
    derivedSupportedSectionsCompRestrictUnit T U RH aH ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (derivedSupportedSectionsRestrictNatIso T U RH aH RH' aH').hom =
      (supportedSectionsRestrictHomotopyIso T U).hom ≫
        derivedRestrictCompSupportedSectionsUnit T U RH' aH' :=
  have := isRightDerivedFunctor_derivedSupportedSectionsComp T U RH aH
  have := isRightDerivedFunctor_restrictCompSupportedSections T U RH' aH'
  Functor.rightDerivedNatTrans_fac
    (RH ⋙ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory)
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⋙ RH')
    (derivedSupportedSectionsCompRestrictUnit T U RH aH)
    (derivedRestrictCompSupportedSectionsUnit T U RH' aH')
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (supportedSectionsRestrictHomotopyIso T U).hom

/-- **The defining factorization, at one object.**  The componentwise form of
`derivedSupportedSectionsRestrictNatIso_fac`, which is what a consumer computing the comparison
after a derivation unit at a single complex of `𝒪_X`-modules uses. -/
theorem derivedSupportedSectionsRestrictNatIso_hom_app
    [RH.IsRightDerivedFunctor aH (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [RH'.IsRightDerivedFunctor aH'
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))]
    (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (derivedSupportedSectionsCompRestrictUnit T U RH aH).app K ≫
        (derivedSupportedSectionsRestrictNatIso T U RH aH RH' aH').hom.app
          (DerivedCategory.Qh.obj K) =
      (supportedSectionsRestrictHomotopyIso T U).hom.app K ≫
        (derivedRestrictCompSupportedSectionsUnit T U RH' aH').app K :=
  NatTrans.congr_app (derivedSupportedSectionsRestrictNatIso_fac T U RH aH RH' aH') K

end Derived

end Stacks.Cohomology.SupportedComplexes

end
