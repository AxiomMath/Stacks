module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSheafHomPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The module-universe comparison on the derived category of the small étale ringed site

Let `S` be a scheme. On the small étale ringed site of `S` the two sides of Stacks 08JP are
objects of derived categories of sheaves of `𝒪`-modules at *different* module universes:
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleDerivedSheafHom`, the left-hand side
`ε^* RSheafHom_{𝒪_S}(E, F)`, lies in `D(Mod_u(𝒪))`, while
`AlgebraicGeometry.SmallEtale.derivedSheafHom`, the right-hand side `RSheafHom(ε^* E, ε^* F)`,
lies in `D(Mod_{u+1}(𝒪))` — the internal Hom complex of Stacks 0A8X raises the module universe on
a site whose objects form a type in `Type (u + 1)`.

This file builds the functor that closes that gap:

`Λ : D(Mod_u(𝒪)) ⥤ D(Mod_{u+1}(𝒪))`,

the derived functor of the universe lift `Stacks.SheafOfModules.moduleULift` of sheaves of
modules, and applies it to the left-hand side. After that the two sides of 08JP are objects of
one and the same category, which is the first of the two things the statement of that tag needs.

## Main definitions

* `AlgebraicGeometry.SmallEtale.ringedSiteModuleULift`: the universe lift
  `Mod_u(𝒪) ⥤ Mod_{u+1}(𝒪)` of sheaves of modules on the small étale ringed site of `S`.
* `AlgebraicGeometry.SmallEtale.derivedModuleULift`: **the module-universe comparison
  `D(Mod_u(𝒪)) ⥤ D(Mod_{u+1}(𝒪))`**, the derived functor of the previous one.
* `AlgebraicGeometry.SmallEtale.derivedModuleULiftFactors`: that comparison computed on a
  complex, namely the degreewise universe lift.
* `AlgebraicGeometry.SmallEtale.raisedDerivedAssociatedModuleDerivedSheafHom`:
  **`Λ (ε^* RSheafHom_{𝒪_S}(E, F))`**, the left-hand side of Stacks 08JP moved into the module
  universe of the right-hand side.
* `AlgebraicGeometry.SmallEtale.derivedSheafHomOfAssociatedModule`:
  **`RSheafHom_𝒪(ε^* E, ε^* F)`**, the right-hand side of Stacks 08JP, at the same stated type.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_ringedSiteModuleULift` and
  `AlgebraicGeometry.SmallEtale.preservesFiniteColimits_ringedSiteModuleULift`: the universe lift
  is exact, which together with its additivity is what gives it a derived functor.
* `AlgebraicGeometry.SmallEtale.raisedDerivedAssociatedModuleDerivedSheafHom_eq`: the raised
  left-hand side is `Λ` applied to the left-hand side, by definition.

## What is *not* here

No map between the two sides. Having both sides of Stacks 08JP in one category is necessary for
the tag to be statable and is not sufficient: the canonical map of Stacks 08JF/08I3 is built from
a tensor–internal-Hom bijection and the monoidality of the pullback, and at the mixed universes of
`ε` neither of those data exists in this development. The abstract shape of the map that *would*
do it, with its agreement with the equal-universe construction, is
`Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison`; see the notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.MixedInternalHomPullbackMap` for the
three data that are missing.

## Implementation notes

The universe lift used is `Stacks.SheafOfModules.moduleULift`, the one at which
`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso` identifies the internal Hom sheaf of
`AlgebraicGeometry.SmallEtale.internalHomSheaf` with that of
`AlgebraicGeometry.RingedSite.internalHomSheaf`.

Additivity of the lift is
`Stacks.SheafOfModules.instAdditiveSheafOfModulesModuleULift`, left exactness is
`Stacks.SheafOfModules.preservesFiniteLimits_moduleULift`, and right exactness is
`Stacks.SheafOfModules.preservesFiniteColimits_moduleULift`; only the last of the three is new.
The two exactness facts are restated at the spelling of the ringed site, as the sheafification
facts of `StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleRingedSiteInternalHom.lean` are,
and made `local instance`s. Both classes are `Prop`s, so a second route to either cannot produce
incompatible data.

The two `HasDerivedCategory` arguments are hypotheses, exactly as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteDerivedInternalHom`:
`CategoryTheory.HasDerivedCategory` is data, and their localization universes differ — `u + 1` for
the module sheaves with sections in `u` and `u + 2` for those with sections in `u + 1`. They are
inhabited by `AlgebraicGeometry.SmallEtale.hasDerivedCategory_sheafOfModules` and its `_raised`
companion.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The universe lift of module sheaves on the small étale ringed site, and its exactness -/

/-- The universe lift `Mod_u(𝒪) ⥤ Mod_{u+1}(𝒪)` of sheaves of `𝒪`-modules on the small étale
ringed site of `S`: the sections are replaced by their `ULift` into `Type (u + 1)`, the site and
the sheaf of rings staying as they are.

This is `Stacks.SheafOfModules.moduleULift` at the lift `u + 1`, which is the lift at which
`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso` reads the internal Hom sheaf of the
ringed site down a universe. -/
public abbrev ringedSiteModuleULift :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O) ⥤
      SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O) :=
  Stacks.SheafOfModules.moduleULift.{u + 1, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)

/-- The universe lift of module sheaves on the small étale ringed site of `S` is left exact.

This is `Stacks.SheafOfModules.preservesFiniteLimits_moduleULift`, restated at the projections of
`AlgebraicGeometry.smallEtaleRingedSite`; finite limits of module sheaves are computed on the
underlying presheaves of abelian groups, where the lift is postcomposition with
`AddCommGrpCat.uliftFunctor`. -/
@[sga "4 V 1.9" "clause 1, special case"]
public theorem preservesFiniteLimits_ringedSiteModuleULift :
    PreservesFiniteLimits (ringedSiteModuleULift B S hS) :=
  Stacks.SheafOfModules.preservesFiniteLimits_moduleULift

/-- The universe lift of module sheaves on the small étale ringed site of `S` is right exact.

This is `Stacks.SheafOfModules.preservesFiniteColimits_moduleULift`, restated at the projections
of `AlgebraicGeometry.smallEtaleRingedSite`. Unlike left exactness this is not objectwise: a
colimit of module sheaves is a sheafification, and what carries it is that the universe lift of
abelian groups commutes with sheafification. -/
public theorem preservesFiniteColimits_ringedSiteModuleULift :
    PreservesFiniteColimits (ringedSiteModuleULift B S hS) :=
  Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{u + 1, u} _

attribute [local instance] preservesFiniteLimits_ringedSiteModuleULift
  preservesFiniteColimits_ringedSiteModuleULift

/-! ### The comparison on derived categories -/

section Comparison

variable [HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))]
  [HasDerivedCategory.{u + 2}
    (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))]

/-- **The module-universe comparison `D(Mod_u(𝒪)) ⥤ D(Mod_{u+1}(𝒪))` on the small étale ringed
site of `S`**: the derived functor of the universe lift of module sheaves.

The lift is additive and exact, so this is
`CategoryTheory.Functor.mapDerivedCategory`, the derived functor of an exact functor, and carries
that construction's triangulated structure. It is the functor in which the left-hand side of
Stacks 08JP can be compared with the right-hand side, the latter living one module universe up
because the internal Hom complex of Stacks 0A8X raises it on this site. -/
public def derivedModuleULift :
    DerivedCategory
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ⥤
      DerivedCategory
        (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :=
  (ringedSiteModuleULift B S hS).mapDerivedCategory

/-- The module-universe comparison on the class of a complex is the class of the degreewise
universe lift of that complex. -/
public def derivedModuleULiftFactors :
    DerivedCategory.Q ⋙ derivedModuleULift B S hS ≅
      (ringedSiteModuleULift B S hS).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (ringedSiteModuleULift B S hS).mapDerivedCategoryFactors

end Comparison

/-! ### The left-hand side of Stacks 08JP in the module universe of the right-hand side -/

section Sides

attribute [local instance] HasDerivedCategory.standard

variable [PreservesFiniteLimits (associatedModuleOfSheaf B S hS)]

/-- **`Λ (ε^* RSheafHom_{𝒪_S}(E, F))`: the left-hand side of Stacks 08JP in the module universe of
the right-hand side.**

For objects `E` and `F` of the derived category of sheaves of `𝒪_S`-modules on the Zariski site of
`S`, this and `AlgebraicGeometry.SmallEtale.derivedSheafHom` applied to the images of `E` and `F`
under `ε^*` are objects of one and the same derived category
`D(Mod_{u+1}(𝒪))`, which they were not before. No map between them is constructed. -/
public def raisedDerivedAssociatedModuleDerivedSheafHom
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    DerivedCategory
      (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :=
  (derivedModuleULift B S hS).obj (derivedAssociatedModuleDerivedSheafHom B S hS E F)

/-- The raised left-hand side of Stacks 08JP is the module-universe comparison applied to the
left-hand side, by definition. -/
public theorem raisedDerivedAssociatedModuleDerivedSheafHom_eq
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    raisedDerivedAssociatedModuleDerivedSheafHom B S hS E F =
      (derivedModuleULift B S hS).obj
        (derivedAssociatedModuleDerivedSheafHom B S hS E F) := rfl

/-- **`RSheafHom_𝒪(ε^* E, ε^* F)`, the right-hand side of Stacks 08JP**, at the arguments that tag
takes: the derived internal Hom of the small étale ringed site of `S` applied to the inverse
images along `ε` of two objects of the derived category of sheaves of `𝒪_S`-modules on the
Zariski site.

Its stated type is the same as that of
`AlgebraicGeometry.SmallEtale.raisedDerivedAssociatedModuleDerivedSheafHom`, which is the point:
the two sides of Stacks 08JP are objects of one and the same derived category, so an equation
between them is now a well-formed proposition. None is proved, and no map between them is
constructed. -/
public def derivedSheafHomOfAssociatedModule
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    DerivedCategory
      (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :=
  derivedSheafHom B S hS ((derivedAssociatedModuleFunctor B S hS).obj E)
    ((derivedAssociatedModuleFunctor B S hS).obj F)

end Sides

end AlgebraicGeometry.SmallEtale

end
