module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleSheafCondition

/-!
# Finite local freeness of the module `Mᵃ` on the slice at an étale chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `W` be an
étale scheme chart of `X`, and let `M` be a quasi-coherent module on the scheme `chartScheme W`
underlying the chart.  The slice of the small étale site of `X` at `W` carries the module `Mᵃ` of
Stacks 03DU, `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`.

**This file proves that `Mᵃ` is finite locally free on the site exactly when `M` is finite
locally free on the chart's scheme.**  That is the clause 03DL (2) of Stacks 05VG, read on the
slice at a chart rather than on the small étale site of a scheme: the Zariski versus small étale
comparison of finite local freeness, transported to the place where a statement about an
algebraic space meets a statement about the scheme of a chart.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_chartModuleReindex_iff`: finite local
  freeness of a module on the slice at a chart is unchanged by the reindexing of Stacks 04M0 onto
  the small étale site of the chart space.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sliceAssociatedModule_iff`: **`Mᵃ` on the
  slice at `W` is finite locally free if and only if `M` is.**

## The route

Four known links compose, and no geometry is added.

1. `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_chartModuleReindex_iff`, proved here, is
   `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff` — Stacks 03DM — at the
   localization of Stacks 04M0, in the spelling
   `AlgebraicGeometry.Space.chartModuleReindexEquivalence`.  It is the general-module form of
   `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff`, which is
   the same statement for a module arising as the restriction of an `𝒪_X`-module and so cannot be
   applied to `Mᵃ`, which does not.
2. `AlgebraicGeometry.Space.chartModuleReindex_sliceAssociatedModule` — an *equality* — rewrites
   the reindexed `Mᵃ` as the reading, on the small étale site of the chart *space*, of the
   pullback-sections sheaf of `M` on the small étale site of the chart *scheme*.
3. `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff` — Stacks
   03DM again, at the comparison of Stacks 03DX (2) — strips that reading.
4. `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules` — Stacks 070S (2) —
   identifies the pullback-sections sheaf with `(-)ᵃ` on the small étale site of the chart's
   scheme, and
   `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff` — Stacks 05VG
   for the clause 03DL (2) at `τ = étale`, both halves — is the comparison itself.

## Implementation notes

Link 1 is stated for `AlgebraicGeometry.Space.chartModuleReindexEquivalence` rather than for
`AlgebraicGeometry.Space.chartSmallEtaleRestriction` because `Mᵃ` is a module of the slice which
is not the restriction of a module on `X`; the two agree on the modules that are, by
`AlgebraicGeometry.Space.chartModuleReindexEquivalence_functor_obj`, which is `rfl`.  Every
continuity and dense-subsite datum is supplied positionally, exactly as
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff` supplies them
and for the same reason: the chart's slice arrives at two spellings of its topology which
instance search does not identify.

No `@[stacks]` attribute is placed.  Stacks 05VG and the clause 03DL (2) are carried by
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff`, of which this is
the transport to the slice at a chart; Stacks 03DM is carried by the two reindexings this
composes.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (W : SmallEtale B S hS X.1)

/-- **Finite local freeness of a module on the slice at a chart is invariant under the
localization of Stacks 04M0.**  This is the general-module form of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff`, which states
the same for a module arising as the restriction of an `𝒪_X`-module. -/
@[stacks 03DM "finite locally free, at the localization of 04M0 at a chart, for a general module \
of the slice"]
theorem isFiniteLocallyFreeOnSite_chartModuleReindex_iff
    (N : SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
        ((chartModuleReindexEquivalence B S hS X W).functor.obj N) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite N :=
  @Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over W)
    (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 W)
    (isContinuous_chartLocalization_chartSpace B S hS X W)
    ((structureRingSheaf B S hS X).over W)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X W)
    N

/-- **The module `Mᵃ` on the slice at an étale chart is finite locally free exactly when `M`
is.**  For a quasi-coherent module `M` on the scheme of an étale chart `W` of an algebraic space
`X`, the module `Mᵃ` of Stacks 03DU formed on the slice of the small étale site of `X` at `W` is
finite locally free on the site if and only if `M` is a finite locally free module on
`chartScheme W`.

This is the clause 03DL (2) of Stacks 05VG — `(-)ᵃ` reflects and preserves finite local freeness
on the small étale site of a scheme — carried across the two comparisons of Stacks 04M0 and
Stacks 03DX (2) to the slice at a chart, as the module documentation describes. -/
theorem isFiniteLocallyFreeOnSite_sliceAssociatedModule_iff (M : (chartScheme W).Modules)
    [M.IsQuasicoherent] :
    SheafOfModules.IsFiniteLocallyFreeOnSite
        (SmallEtale.sliceAssociatedModule B S hS X.1 X.2 W M
          (SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent B S hS X.1 W M)) ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  -- Link 4: Stacks 070S (2), then Stacks 05VG for the clause 03DL (2).
  have e := _root_.AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules
    (associatedBigEtaleSite B) (chartScheme W)
    ((SmallEtale.toOver B S hS X.1).obj W).left.property M
  have hassoc : SheafOfModules.IsFiniteLocallyFreeOnSite
      (_root_.AlgebraicGeometry.SmallEtale.sectionsSheafOfModules (associatedBigEtaleSite B)
        (chartScheme W) ((SmallEtale.toOver B S hS X.1).obj W).left.property M) ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    (Iff.intro (SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e.symm)
        (SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e)).trans
      (_root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff
        (associatedBigEtaleSite B) (chartScheme W)
        ((SmallEtale.toOver B S hS X.1).obj W).left.property M)
  -- Link 3: the comparison of Stacks 03DX (2) at the chart.
  have hrep := isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS
    ((SmallEtale.toOver B S hS X.1).obj W)
    (_root_.AlgebraicGeometry.SmallEtale.sectionsSheafOfModules (associatedBigEtaleSite B)
      (chartScheme W) ((SmallEtale.toOver B S hS X.1).obj W).left.property M)
  -- Link 1, then link 2 as a rewrite.
  refine (isFiniteLocallyFreeOnSite_chartModuleReindex_iff B S hS X W
    (SmallEtale.sliceAssociatedModule B S hS X.1 X.2 W M
      (SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent
        B S hS X.1 W M))).symm.trans ?_
  rw [chartModuleReindex_sliceAssociatedModule B S hS X W M]
  exact hrep.trans hassoc

end AlgebraicGeometry.Space

end
