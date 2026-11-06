module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueModulesAreAcyclic
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveFlasqueModules

/-!
# Derived sections of a complex of modules on a scheme

Let `X` be a scheme and `U` an open subscheme. Taking sections over `U` is a left exact functor
`Γ(U, -) : X.Modules ⥤ ModuleCat Γ(X, U)`, not an exact one, so it does not descend to derived
categories on the nose. Its total right derived functor is `RΓ(U, -)`, the functor whose
cohomology objects are the cohomology modules `H^i(U, -)`.

This file constructs that functor on the **bounded below** derived category, which is where the
source itself places it (the diagram of Stacks 01FM has `D^{+}(X)` as the source of `RΓ(X, -)`).
The construction is Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus`; the two inputs it
needs are that `Γ(U, -)` is additive and that `X.Modules` has enough injectives, and the second
holds because `X.Modules` is a Grothendieck abelian category.

## Main definitions

* `Stacks.Cohomology.sectionsFunctor X U` is `Γ(U, -) : X.Modules ⥤ ModuleCat Γ(X, U)`.
* `Stacks.Cohomology.derivedSections X U` is `RΓ(U, -) : D⁺(X.Modules) ⥤ D⁺(ModuleCat Γ(X, U))`.
* `Stacks.Cohomology.derivedSectionsUnit X U` is the natural transformation exhibiting
  `derivedSections X U` as a right derived functor of `sectionsFunctor X U`.
* `Stacks.Cohomology.derivedGlobalSections X` is `RΓ(X, -)`, the case `U = ⊤`.

## Main results

* `Stacks.Cohomology.preservesFiniteLimits_sectionsFunctor`: sections over an open are left exact.
  This is why a *right* derived functor is the right notion here.
* `Stacks.Cohomology.isRightDerivedFunctor_derivedSections`: `derivedSections X U` together with
  `derivedSectionsUnit X U` is a right derived functor of `sectionsFunctor X U`, i.e. a left Kan
  extension of it along the localisation. This universal property is what pins the functor down:
  it is not merely some functor computing the right cohomology modules. Through it, Mathlib's
  instance for right derived functors on `HomotopyCategory.Plus`
  (`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`) makes the unit an
  isomorphism on a bounded below complex of injective `𝒪_X`-modules, so such a complex computes
  `RΓ(U, -)`.

## Implementation notes

The ambient category is `AlgebraicGeometry.Scheme.Modules`, written `X.Modules`, and **not**
`SheafOfModules X.ringCatSheaf`. The two are definitionally the same type, but `X.Modules` carries
its own `CategoryTheory.Category` instance, so they are different objects as far as typeclass
resolution is concerned, and the choice matters in both directions here:

* `EnoughInjectives X.Modules` *is* found by instance search, because Mathlib records
  `IsGrothendieckAbelian.{u} X.Modules` directly
  (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`). At the `SheafOfModules X.ringCatSheaf`
  spelling the same search fails: `X.ringCatSheaf` is a `CategoryTheory.sheafCompose`, and
  instance resolution will not unfold it at reducible transparency. So the headline definitions
  here live at `X.Modules`.
* `(SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive`, conversely, is *not* found by
  instance search at `X.ringCatSheaf`, for the same reason read in the other direction: the
  instance that applies is about the unfolded composite
  `SheafOfModules.forget ⋙ PresheafOfModules.evaluation`. The cure is the standard one — state
  the fact at a variable sheaf of rings and apply it as a term, where the identification is
  checked at default transparency. `Stacks.Cohomology.FlasqueAcyclic.evaluation_additive` is
  exactly that statement, so it is reused rather than restated.

Mathlib's `rightDerivedFunctorPlus` is not yet known to be triangulated (that is a `TODO` in
`Mathlib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`), so no triangulated
structure is asserted here either.

An *unbounded* `RΓ(U, -)` is also available, as
`AlgebraicGeometry.derivedSectionsUnbounded`: sheaves of `𝒪_X`-modules are a Grothendieck
abelian category, so `Stacks.Injectives.kInjectiveResolutionInclusion` gives K-injective
resolutions of arbitrary cochain complexes and the total right derived functor of sections exists
on `D(𝒪_X)`. The functor built here is the bounded below one because that is where the source
places `RΓ(X, -)` (the diagram of Stacks 01FM has `D^{+}(X)` as its source), and the two agree on
`D⁺` by `AlgebraicGeometry.derivedSectionsUnboundedιIso`.

## References

* [The Stacks Project, Section 20.3 (01FP)](https://stacks.math.columbia.edu/tag/01FP)
* [The Stacks Project, Lemma 20.21.1 (01FM)](https://stacks.math.columbia.edu/tag/01FM)
* [The Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) (U : X.Opens)

/-- Sections over an open subscheme `U`, as a functor from `𝒪_X`-modules to `Γ(X, U)`-modules.
This is Mathlib's `AlgebraicGeometry.SheafOfModules.evaluation` at `U`, read at the scheme-level
spelling `X.Modules` of the category of `𝒪_X`-modules. -/
def sectionsFunctor : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

/-- Sections over an open are additive.

This is `Stacks.Cohomology.FlasqueAcyclic.evaluation_additive`, applied as a term: at the
`sheafCompose` expression `X.ringCatSheaf` instance search does not find it. -/
instance sectionsFunctor_additive : (sectionsFunctor X U).Additive :=
  Stacks.Cohomology.FlasqueAcyclic.evaluation_additive X.ringCatSheaf (op U)

/-- Sections over an open are left exact. This is the reason the derived functor taken below is a
*right* derived functor; sections are not right exact, and the failure is what sheaf cohomology
measures. -/
instance preservesFiniteLimits_sectionsFunctor :
    PreservesFiniteLimits (sectionsFunctor X U) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op U)))

/-- `RΓ(U, -)`, the derived sections over an open subscheme `U`, as a functor from the bounded
below derived category of `𝒪_X`-modules to the bounded below derived category of
`Γ(X, U)`-modules.

It is the total right derived functor of `Stacks.Cohomology.sectionsFunctor`, which exists
because `X.Modules` is a Grothendieck abelian category and so has enough injectives. Its
cohomology objects are the cohomology modules `H^i(U, -)`. -/
def derivedSections :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus (ModuleCat.{u} Γ(X, U)) :=
  (sectionsFunctor X U).rightDerivedFunctorPlus

/-- The natural transformation `Γ(U, -) ⟶ RΓ(U, -)` of the derived functor
`Stacks.Cohomology.derivedSections`, comparing the sections of a bounded below complex with its
derived sections. -/
def derivedSectionsUnit :
    (sectionsFunctor X U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedSections X U :=
  (sectionsFunctor X U).rightDerivedFunctorPlusUnith

/-- `Stacks.Cohomology.derivedSections` is a right derived functor of
`Stacks.Cohomology.sectionsFunctor`, with comparison map
`Stacks.Cohomology.derivedSectionsUnit`: that is, the latter exhibits the former as a left Kan
extension along the localisation of the homotopy category at the quasi-isomorphisms.

This universal property is the content of the definition: `derivedSections X U` is not some
functor whose cohomology happens to be sheaf cohomology, it is *the* derived functor of sections,
determined up to unique isomorphism by this property. -/
instance isRightDerivedFunctor_derivedSections :
    (derivedSections X U).IsRightDerivedFunctor (derivedSectionsUnit X U)
      (HomotopyCategory.Plus.quasiIso X.Modules) := by
  dsimp only [derivedSections, derivedSectionsUnit]
  infer_instance

/-- `RΓ(X, -)`, the derived global sections of a bounded below complex of `𝒪_X`-modules, as a
functor to the bounded below derived category of `Γ(X, X)`-modules. It is
`Stacks.Cohomology.derivedSections` at the total open. -/
abbrev derivedGlobalSections :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus (ModuleCat.{u} Γ(X, ⊤)) :=
  derivedSections X ⊤

end Stacks.Cohomology

end
