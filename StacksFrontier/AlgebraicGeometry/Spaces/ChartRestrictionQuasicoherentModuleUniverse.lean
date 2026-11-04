module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse

/-!
# The chart restriction of Stacks 04M0 at a free module universe

`AlgebraicGeometry.Space.chartSmallEtaleRestriction` reads the restriction of an `𝒪_X`-module to
an étale scheme chart as a module on the small étale site of that chart, and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction_iff` transports
quasi-coherence across that reading.  Both are stated for a module whose sections lie in the
universe `u` of the schemes, because
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` is.

This file states them with the module universe free.

## Main definitions

* `AlgebraicGeometry.Space.chartSmallEtaleRestriction'`:
  `AlgebraicGeometry.Space.chartSmallEtaleRestriction` with the module universe free.  Its value
  is an `AlgebraicGeometry.Space.Modules` of the chart, the two structure sheaves being the same
  by `AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_over_of_chartSmallEtaleRestriction'`:
  **quasi-coherence of a module on the small étale site of an étale scheme chart is
  quasi-coherence of the slice it came from**, at a free module universe.

## Implementation notes

Only the direction from the chart to the slice is stated, the direction
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex'` supplies.  The converse direction at a
free module universe would need the transport of a global presentation along the comparison in
the other direction, which is `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex'` applied
to the inverse equivalence.

The definition is the pinned one verbatim, with the universe of the module sections replaced; no
instance argument changes, since the module universe enters
`CategoryTheory.SheafOfModules.pushforward` only through the module it is applied to.  The two
sites have objects in `Type (u + 1)` and morphisms in `Type u`, which is the equi-universe shape
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex'` asks of them.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The restriction of an `𝒪_X`-module to an étale scheme chart `U`, read as a module on the
small étale site of `U` through the comparison equivalence of Stacks 04M0, with the universe of
the module sections independent of the universe of the schemes.

This is `AlgebraicGeometry.Space.chartSmallEtaleRestriction` with that universe left free. -/
noncomputable def chartSmallEtaleRestriction'
    (M : SheafOfModules.{m} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1) :
    Modules.{u, m} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2 :=
  (@SheafOfModules.pushforward _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor
    (chartStructureRingSheaf B S hS X U)
    ((structureRingSheaf B S hS X).over U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    (𝟙 _)).obj (M.over U)

/-- **Quasi-coherence on the small étale site of an étale scheme chart gives quasi-coherence on
the slice at that chart**, at a free module universe. -/
theorem isQuasicoherentOnSite_over_of_chartSmallEtaleRestriction'
    (M : SheafOfModules.{m} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1)
    (h : (chartSmallEtaleRestriction' B S hS X M U).IsQuasicoherentOnSite) :
    (M.over U).IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex' _ _ _ _ _ _
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    ((structureRingSheaf B S hS X).over U)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U) (M.over U) h

end AlgebraicGeometry.Space

end
