module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.TwoOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget

/-!
# The spellings of restriction to an open

Restriction of modules to an open subspace, and the functor it induces on derived categories,
is written in five ways in this development, as distinct constants:

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` along
  `AlgebraicGeometry.RingedSpace.ofRestrict`, equivalently
  `Stacks.Cohomology.GlueingComplexes.derivedRestrict`;
* `Stacks.Cohomology.HigherDirectImage.moduleRestriction`;
* `AlgebraicGeometry.RingedSpace.restrictModules`;
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`;
* `AlgebraicGeometry.Scheme.Modules.restrictFunctor` along `U.ι`, Mathlib's restriction along an
  open immersion of schemes.

This file identifies them, together with the ambient categories they are stated over.

## Main results

* `Stacks.RestrictionSpellings.moduleRestriction_eq_pseudoCoherenceRestrictModules`,
  `Stacks.RestrictionSpellings.moduleRestriction_eq_ringedSpaceRestrictModules` and
  `Stacks.RestrictionSpellings.pseudoCoherenceRestrictModules_eq_ringedSpaceRestrictModules`:
  the three ringed-space spellings are equal by `rfl`, target categories included.
* `Stacks.RestrictionSpellings.moduleRestriction_eq_restrictFunctor` and
  `Stacks.RestrictionSpellings.ringedSpaceRestrictModules_eq_restrictFunctor`: each of them is
  Mathlib's restriction along `U.ι`, as an equality of functors.
* `Stacks.RestrictionSpellings.moduleRestrictionDerivedIsoRestrictFunctor` and
  `Stacks.RestrictionSpellings.derivedPullbackIsoRestrictFunctor`: the corresponding
  isomorphisms on derived categories.
* `Stacks.RestrictionSpellings.restrictToOpen_eq_restrict`,
  `Stacks.RestrictionSpellings.toRingedSpace_eq_restrict` and the `Modules`/`OXMod` equalities:
  the identifications of the ambient objects.

## Implementation notes

On derived categories the identifications are isomorphisms, not equalities:
`CategoryTheory.Functor.mapDerivedCategory` takes preservation of finite limits and colimits as
instance arguments, and `CategoryTheory.Limits.PreservesFiniteColimits` is data, so an equality
of functors does not transport and `rfl` fails there. The isomorphism is
`CategoryTheory.Functor.mapDerivedCategoryCongr`, as applied in
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`.

The derived categories are taken at `CategoryTheory.HasDerivedCategory.standard` throughout.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.HigherDirectImage (moduleRestriction restrictToOpen)

universe u

namespace Stacks.RestrictionSpellings

attribute [local instance] HasDerivedCategory.standard

/-! ### The ambient objects -/

section Ambient

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- The categories of sheaves of modules over `AlgebraicGeometry.structureSheafRing X` and over
`StrictlyPerfect.structureSheafOfRings X` coincide: both sheaves of rings are `X.presheaf` with
commutativity forgotten. -/
theorem sheafOfModules_structureSheafRing_eq_oxMod :
    SheafOfModules.{u} (structureSheafRing X) = OXMod.{u, u, u} X := rfl

/-- `Stacks.Cohomology.HigherDirectImage.restrictToOpen X U` is
`AlgebraicGeometry.SheafedSpace.restrict` along the open embedding of `U`. -/
theorem restrictToOpen_eq_restrict : restrictToOpen X U = X.restrict U.isOpenEmbedding := rfl

/-- `Stacks.Cohomology.GlueingComplexes.DerivedModules X` is the derived category of
`StrictlyPerfect.OXMod X`. -/
theorem derivedModules_eq_derivedCategory_oxMod :
    Stacks.Cohomology.GlueingComplexes.DerivedModules X =
      DerivedCategory (OXMod.{u, u, u} X) := rfl

end Ambient

/-! ### The three ringed-space spellings -/

section RingedSpaceSpellings

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- `Stacks.Cohomology.HigherDirectImage.moduleRestriction` is
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`. -/
theorem moduleRestriction_eq_pseudoCoherenceRestrictModules :
    moduleRestriction X U =
      AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U := rfl

/-- `Stacks.Cohomology.HigherDirectImage.moduleRestriction` is
`AlgebraicGeometry.RingedSpace.restrictModules`. -/
theorem moduleRestriction_eq_ringedSpaceRestrictModules :
    moduleRestriction X U = AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X U := rfl

/-- `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` is
`AlgebraicGeometry.RingedSpace.restrictModules`. -/
theorem pseudoCoherenceRestrictModules_eq_ringedSpaceRestrictModules :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U =
      AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X U := rfl

end RingedSpaceSpellings

/-! ### Crossing to the scheme-level restriction -/

section Scheme

variable (X : Scheme.{u}) (U : X.Opens)

/-- The ringed space of an open subscheme `U` is the open subspace
`AlgebraicGeometry.SheafedSpace.restrict` of the ambient ringed space along `U`. -/
theorem toRingedSpace_eq_restrict :
    U.toScheme.toRingedSpace = X.toRingedSpace.restrict U.isOpenEmbedding := rfl

/-- The `𝒪_X`-modules on a scheme `X` are the `𝒪_X`-modules `StrictlyPerfect.OXMod` on its
ringed space. -/
theorem modules_eq_oxMod : X.Modules = OXMod.{u, u, u} X.toRingedSpace := rfl

/-- The `𝒪_U`-modules on an open subscheme `U` are the modules `StrictlyPerfect.OXMod` on the
open subspace of the ambient ringed space. -/
theorem modules_toScheme_eq_oxMod :
    U.toScheme.Modules = OXMod.{u, u, u} (X.toRingedSpace.restrict U.isOpenEmbedding) := rfl

/-- The derived category of `X.Modules` is the derived category of
`StrictlyPerfect.OXMod X.toRingedSpace`. -/
theorem derivedCategory_modules_eq_oxMod :
    DerivedCategory X.Modules = DerivedCategory (OXMod.{u, u, u} X.toRingedSpace) := rfl

/-- The derived category of `𝒪_U`-modules on an open subscheme `U` is the derived category of
`StrictlyPerfect.OXMod` on the open subspace of the ambient ringed space. -/
theorem derivedCategory_modules_toScheme_eq_oxMod :
    DerivedCategory U.toScheme.Modules =
      DerivedCategory (OXMod.{u, u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) := rfl

/-- `Stacks.Cohomology.GlueingComplexes.DerivedModules X.toRingedSpace` is the derived category
of `X.Modules`. -/
theorem derivedModules_eq_derivedCategory_modules :
    Stacks.Cohomology.GlueingComplexes.DerivedModules X.toRingedSpace =
      DerivedCategory X.Modules := rfl

/-- `Stacks.Cohomology.GlueingComplexes.derivedRestrict` along the inclusion of an open subspace
is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` along it. -/
theorem derivedRestrict_eq_derivedPullback :
    Stacks.Cohomology.GlueingComplexes.derivedRestrict
        (X.toRingedSpace.ofRestrict U.isOpenEmbedding) =
      derivedPullback (X.toRingedSpace.ofRestrict U.isOpenEmbedding) := rfl

/-- `Stacks.Cohomology.HigherDirectImage.moduleRestriction` on a scheme is Mathlib's restriction
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`, as an equality of functors. -/
theorem moduleRestriction_eq_restrictFunctor :
    moduleRestriction X.toRingedSpace U = Scheme.Modules.restrictFunctor U.ι :=
  Stacks.Perfect.BoundedLocallyFreeComplexes.restrictModules_eq_restrictFunctor X U

/-- `AlgebraicGeometry.RingedSpace.restrictModules` on a scheme is Mathlib's restriction
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`, as an equality of functors. -/
theorem ringedSpaceRestrictModules_eq_restrictFunctor :
    AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace U =
      Scheme.Modules.restrictFunctor U.ι :=
  Stacks.Perfect.BoundedLocallyFreeComplexes.restrictModules_eq_restrictFunctor X U

/-- The functor induced by `Stacks.Cohomology.HigherDirectImage.moduleRestriction` on derived
categories is isomorphic to the one induced by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`. -/
def moduleRestrictionDerivedIsoRestrictFunctor :
    (moduleRestriction X.toRingedSpace U).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
  AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X U

/-- The derived pullback along the inclusion of an open subscheme `U` is isomorphic to the functor
induced on derived categories by `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`. -/
def derivedPullbackIsoRestrictFunctor :
    derivedPullback (X.toRingedSpace.ofRestrict U.isOpenEmbedding) ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
  Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso
      X.toRingedSpace U ≪≫
    moduleRestrictionDerivedIsoRestrictFunctor X U

end Scheme

end Stacks.RestrictionSpellings

end
