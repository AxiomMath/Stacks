module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSemilinear

/-!
# The two spellings of a module on the small étale site of a chart's scheme

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `W` be an
étale scheme chart of `X`.  A module on the slice of the small étale site of `X` at `W` is read on
the small étale site of the scheme underlying `W` in two ways, and the tree carries both:

* `AlgebraicGeometry.Space.chartSchemeSiteModule` is the direct image along the single functor of
  `AlgebraicGeometry.Space.chartSchemeEquivalence`, the comparison of Stacks 04M0 after
  Stacks 03ED;
* the two-leg composite of `AlgebraicGeometry.Space.chartModuleReindexEquivalence`, which
  reindexes along the localization of Stacks 04M0 only, with the *inverse* of
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, which carries the small étale
  site of the chart's scheme to that of the algebraic space the chart represents.

**This file identifies them.**  The identification is what lets a statement proved in the
two-leg spelling — `AlgebraicGeometry.Space.chartModuleReindex_sliceAssociatedModule`, which
computes the module `Mᵃ` of Stacks 03DU there — be read against a statement proved in the
one-functor spelling, such as
`AlgebraicGeometry.Space.chartSchemeSiteModulePushforwardIso`.

## Main results

* `AlgebraicGeometry.Space.chartSchemeSiteModule_eq_inverse_chartModuleReindex`: **the two
  spellings agree**, as an equality of modules.

## Implementation notes

Both sides are a direct image with the *identity* structure map, along functors that are equal
on the nose: `AlgebraicGeometry.Space.chartSchemeEquivalence` is defined as the composite of the
inverse of the represented comparison with the localization of Stacks 04M0, so the composite
functor of the two legs is the single functor of the one-functor spelling by `rfl`.  What is not
free is the structure map: the inverse of an equivalence of ringed sites is a direct image along
`Stacks.SheafOfModules.reindexBackSharp`, the counit of the equivalence read on the structure
sheaf, and not along the identity.  Here that counit does act as the identity — the represented
comparison leaves the underlying scheme of a chart unchanged and the structure sheaf is the
global functions on it — which is the one computation this file performs, and it is `rfl`.

The equality is *not* provable by a single `rfl`: that elaborates the two sides against each
other through `CategoryTheory.Functor.sheafPushforwardContinuous` at long composites of
comparison functors and exhausts the heartbeat budget inside `whnf`.  The proof therefore
collapses the chain abstractly, with `Stacks.SheafOfModules.pushforward_pushforward_obj`, and
performs the computation of the structure map on its own, where it is small; the two legs are
then recognised by `Stacks.SheafOfModules.reindexEquivalence_inverse` and by `rfl` at the
spelling in which every argument of `CategoryTheory.SheafOfModules.pushforward` is given.

Every continuity datum is supplied positionally rather than by instance search.  This is not
decoration: the chart's small étale site arrives at the two spellings
`AlgebraicGeometry.Space.SmallEtale ‹_› (chartSpace ‹_›).1` and
`AlgebraicGeometry.Space.SmallEtale ‹_› (yoneda.obj (chartOverObject ‹_›))`, and the slice at the
two spellings `(AlgebraicGeometry.Space.SmallEtale.topology ‹_›).over W` and
`((smallEtaleRingedSite ‹_›).over W).J`; each pair is equal by `rfl` and not syntactically, so
continuity proved at one spelling is not found by instance search at the other, and the
declaration below would be reported as having no instance for a class whose instance is in scope.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (W : SmallEtale B S hS X.1)

/-- **The two readings of a module on the small étale site of a chart's scheme agree.**  The
direct image of a module on the slice at an étale scheme chart `W` along the single functor of
the comparison of Stacks 04M0 after Stacks 03ED is the two-leg composite: reindex along the
localization of Stacks 04M0 at `W`, then carry the result from the small étale site of the chart
*space* to that of the chart *scheme* by the inverse of the represented comparison.

Both sides are a direct image along one and the same functor — the comparison of Stacks 04M0
after Stacks 03ED is that composite, definitionally — and the structure maps agree because the
counit of the represented comparison acts as the identity on the structure sheaf. -/
theorem chartSchemeSiteModule_eq_inverse_chartModuleReindex
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over W).O)) :
    chartSchemeSiteModule B S hS X W M =
      (representedSmallEtaleModuleEquivalence B S hS (chartOverObject B S hS X W)).inverse.obj
        ((chartModuleReindexEquivalence B S hS X W).functor.obj M) := by
  have hloc : (chartModuleReindexEquivalence B S hS X W).functor =
      @SheafOfModules.pushforward.{u}
        (SmallEtale B S hS (chartSpace B S hS X W).1) _
        ((smallEtaleRingedSite B S hS X.1 X.2).over W).C _
        (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
        ((smallEtaleRingedSite B S hS X.1 X.2).over W).J
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor
        (chartStructureRingSheaf B S hS X W)
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over W).O)
        (isContinuous_chartLocalization_chartSpace B S hS X W)
        (𝟙 _) := rfl
  have hrepr :
      (representedSmallEtaleModuleEquivalence B S hS (chartOverObject B S hS X W)).inverse =
        SheafOfModules.pushforward.{u} (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj (chartOverObject B S hS X W)))
          (representedSmallEtaleEquivalence B S hS (chartOverObject B S hS X W))
          (representedSchemeStructureSheaf B S hS (chartOverObject B S hS X W))) :=
    Stacks.SheafOfModules.reindexEquivalence_inverse _ _
  rw [hrepr, hloc]
  refine Eq.symm ?_
  exact (@Stacks.SheafOfModules.pushforward_pushforward_obj _ _ _ _
        (chartSchemeTopology B S hS X W)
        (SmallEtale.topology B S hS (yoneda.obj (chartOverObject B S hS X W)))
        ((representedSmallEtaleEquivalence B S hS (chartOverObject B S hS X W)).inverse)
        (chartSchemeSiteStructureSheaf B S hS X W)
        (chartStructureRingSheaf B S hS X W)
        (isContinuous_representedSmallEtaleEquivalence_inverse B S hS
          (chartOverObject B S hS X W))
        (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj (chartOverObject B S hS X W)))
          (representedSmallEtaleEquivalence B S hS (chartOverObject B S hS X W))
          (representedSchemeStructureSheaf B S hS (chartOverObject B S hS X W)))
        ((smallEtaleRingedSite B S hS X.1 X.2).over W).C _
        ((smallEtaleRingedSite B S hS X.1 X.2).over W).J
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor
        (isContinuous_chartLocalization_chartSpace B S hS X W)
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over W).O)
        (𝟙 _) M).trans
      (congrArg (fun χ => (@SheafOfModules.pushforward.{u}
          (chartSchemeSite B S hS X W) _
          ((smallEtaleRingedSite B S hS X.1 X.2).over W).C _
          (chartSchemeTopology B S hS X W)
          ((smallEtaleRingedSite B S hS X.1 X.2).over W).J
          ((representedSmallEtaleEquivalence B S hS (chartOverObject B S hS X W)).inverse ⋙
            (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor)
          (chartSchemeSiteStructureSheaf B S hS X W)
          (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over W).O)
          (isContinuous_chartSchemeIdentification_functor B S hS X W) χ).obj M)
        (show Stacks.SheafOfModules.reindexBackSharp
              (J' := SmallEtale.topology B S hS (yoneda.obj (chartOverObject B S hS X W)))
              (representedSmallEtaleEquivalence B S hS (chartOverObject B S hS X W))
              (representedSchemeStructureSheaf B S hS (chartOverObject B S hS X W)) ≫
            ((representedSmallEtaleEquivalence B S hS
              (chartOverObject B S hS X W)).inverse.sheafPushforwardContinuous RingCat.{u}
              (chartSchemeTopology B S hS X W)
              (SmallEtale.topology B S hS (yoneda.obj (chartOverObject B S hS X W)))).map
              (𝟙 (chartStructureRingSheaf B S hS X W)) = 𝟙 _ from rfl))

end AlgebraicGeometry.Space

end
