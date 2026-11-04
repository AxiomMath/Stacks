module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitRestrictScalarsIsoAnySite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp

/-!
# `f_*𝒪_X` is the small-chart base-change direct image of the unit module

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  The direct image `f_*𝒪_X` of Stacks 03ZV, which
`AlgebraicGeometry.Space.pushforwardStructureModule` forms as the direct image of Stacks 03LU
applied to the unit module of `𝒪_X`, is here identified with the direct image of the unit module
along *small-chart base change*, the restriction of sites of
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`.

This is the comparison that
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean` lacks for the module
it carries, at the one module `𝒪_X` — which is the module Stacks 03ZU and Stacks 03ZW are about.

## Main results

* `AlgebraicGeometry.Space.pushforwardStructureModuleIsoSmallBaseChange`: `f_*𝒪_X` is
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` of the unit module.

## The route

Both sides are a restriction of scalars of a unit module.  On the left,
`AlgebraicGeometry.Space.modulePushforward` is the direct image of modules of Stacks 03D1 followed
by restriction of scalars along the structure map `f♯` of Stacks 03G8, and the direct image of the
unit module *is* the unit module of the direct-image sheaf of rings, by
`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`, which is `Iso.refl`.  On the right,
`SheafOfModules.pushforward` is restriction along the functor of sites followed by restriction of
scalars along `AlgebraicGeometry.Space.smallBaseChangeSharp`, and again the unit module goes to
the unit module of the restricted sheaf of rings.

So the comparison drops to the sheaves of rings, where
`AlgebraicGeometry.Space.chartProjectionSharpDirectImage` is an *isomorphism* `f_*𝒪_X ≅ 𝒪_X`
restricted along small-chart base change
(`AlgebraicGeometry.Space.isIso_chartProjectionSharpDirectImage`) through which `f♯` becomes
pullback of regular functions along the cartesian projections
(`AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage`, Stacks 03G8,
part (2)) — and that is `AlgebraicGeometry.Space.smallBaseChangeSharp` itself, on the nose.
Restriction of scalars along an isomorphism of sheaves of rings carries the unit module to the
unit module, which is
`Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIsoOfIsoAnySite`, and restriction of
scalars composes by `rfl`, so the two restrictions of scalars fuse into the one along `f♯`
followed by the isomorphism.

## Implementation notes

`AlgebraicGeometry.Space.cartesianProjectionSharp`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSchemeStructureSharp.lean`) and
`AlgebraicGeometry.Space.smallBaseChangeSharp` are the same morphism by `rfl`, since
`AlgebraicGeometry.Space.cartesianProjectionOver` and
`AlgebraicGeometry.Space.smallBaseChangeProjection` are the same natural transformation and
whiskering by a composite functor is whiskering twice; that is why Stacks 03G8, part (2) can be
used here without a further comparison, and why only the equality of morphisms of sheaves of
rings, and no transport of the sheaf of rings itself, appears below.

This does **not** compare the two direct-image functors at an arbitrary module, and so does not
place the tag of Stacks 04CF on
`AlgebraicGeometry.Space.overFunctor_comp_smallBaseChangeModulePushforward`: the comparison above
runs through `Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`, which is special to the unit
module, and at a general module the sheaf of rings of the direct image still has to be compared
with the direct image of the sheaf of rings as a *ring* structure on the same sections, which is
the first of the two comparisons listed as missing in that file.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The structure map of Stacks 03G8, read through
`AlgebraicGeometry.Space.chartProjectionSharpDirectImage`, is the structure map of small-chart
base change.**  This is Stacks 03G8, part (2) with its right-hand side
`AlgebraicGeometry.Space.cartesianProjectionSharp` recognised as
`AlgebraicGeometry.Space.smallBaseChangeSharp`, the two being the same morphism by `rfl`. -/
theorem structureSharp_comp_chartProjectionSharpDirectImage' (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    structureSharp B S hS f ≫ chartProjectionSharpDirectImage B S hS f hf =
      smallBaseChangeSharp B S hS f hf :=
  structureSharp_comp_chartProjectionSharpDirectImage B S hS f hf

/-- The direct image of the unit module along small-chart base change is the restriction of
scalars, along `AlgebraicGeometry.Space.smallBaseChangeSharp`, of the unit module of the
restricted sheaf of rings: the direct image of sheaves of modules along a restriction of sites
leaves the sections of the unit module alone and only reads them over the smaller ring. -/
theorem smallBaseChangeModulePushforward_unit (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (smallBaseChangeModulePushforward.{u} B S hS f hf).obj
        (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)) =
      (SheafOfModules.restrictScalars.{u} (smallBaseChangeSharp B S hS f hf)).obj
        (SheafOfModules.unit
          (((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
              (smallEtaleRingSheaf B S hS X.1 X.2))) :=
  rfl

/-- Restriction of scalars along the structure map `f♯` of Stacks 03G8 and then along the
isomorphism `AlgebraicGeometry.Space.chartProjectionSharpDirectImage` is restriction of scalars
along `AlgebraicGeometry.Space.smallBaseChangeSharp`, by Stacks 03G8, part (2).  Read at the unit
module, which is where
`AlgebraicGeometry.Space.pushforwardStructureModuleIsoSmallBaseChange` needs it. -/
theorem restrictScalars_chartProjectionSharpDirectImage_unit (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (SheafOfModules.restrictScalars.{u} (structureSharp B S hS f)).obj
        ((SheafOfModules.restrictScalars.{u}
            (chartProjectionSharpDirectImage B S hS f hf)).obj
          (SheafOfModules.unit
            (((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
              (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
                (smallEtaleRingSheaf B S hS X.1 X.2)))) =
      (smallBaseChangeModulePushforward.{u} B S hS f hf).obj
        (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)) :=
  (congrArg
    (fun φ ↦ (SheafOfModules.restrictScalars.{u} φ).obj
      (SheafOfModules.unit
        (((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
            (smallEtaleRingSheaf B S hS X.1 X.2))))
    (structureSharp_comp_chartProjectionSharpDirectImage' B S hS f hf)).trans
      (smallBaseChangeModulePushforward_unit B S hS f hf).symm

/-- **`f_*𝒪_X` is the small-chart base-change direct image of the unit module.**  For a
representable morphism `f : X ⟶ Y` of algebraic spaces, the direct image of the structure sheaf
of `X` of Stacks 03ZV — the direct image of Stacks 03LU applied to the unit module — is the
direct image of the unit module along the restriction of sites of
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`.

The comparison is restriction of scalars along the structure map `f♯` applied to
`Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIsoOfIsoAnySite` at the isomorphism of
sheaves of rings `AlgebraicGeometry.Space.chartProjectionSharpDirectImage`; the resulting composite
of two restrictions of scalars is the one along `f♯` followed by that isomorphism, which is
`AlgebraicGeometry.Space.smallBaseChangeSharp` by Stacks 03G8, part (2). -/
def pushforwardStructureModuleIsoSmallBaseChange (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    pushforwardStructureModule B S hS f ≅
      (smallBaseChangeModulePushforward.{u} B S hS f hf).obj
        (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)) :=
  (SheafOfModules.restrictScalars.{u} (structureSharp B S hS f)).mapIso
      (Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIsoOfIsoAnySite
        (asIso (chartProjectionSharpDirectImage B S hS f hf))) ≪≫
    eqToIso (restrictScalars_chartProjectionSharpDirectImage_unit B S hS f hf)

end AlgebraicGeometry.Space

end
