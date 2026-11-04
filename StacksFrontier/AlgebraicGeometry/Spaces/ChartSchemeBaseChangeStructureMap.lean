module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictPushforward

/-!
# The structure maps of the chart base-change square

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`, let `V` be an
étale scheme chart of `Y` and let `U = V ×_Y X` be the base-changed chart of `X`, with
`ψ : U ⟶ V` the cartesian projection.  `AlgebraicGeometry.Space.chartSchemeBaseChangeIso` fills
the square

```
 chartSchemeSite V --- base change along ψ ---> chartSchemeSite U
        |                                              |
 chartSchemeEquivalence                    chartSchemeEquivalence
        v                                              v
     Over V -------- Over.post (smallBaseChange f) -> Over U
```

with a natural isomorphism of functors of sites.  A square of *ringed* sites needs, besides that
isomorphism, the two composite comparisons of structure sheaves that the two ways round the
square carry.  This file supplies them, together with the continuity instances they are indexed
by, in the spelling in which `SheafOfModules.pushforwardCongr₂` consumes them.

Along the bottom and left the comparison is
`AlgebraicGeometry.Space.chartLocalizedSharp`, the structure map of the localized morphism of
ringed sites of Stacks 04J0 (1) at the chart `V`, preceded by the identity: the two structure
sheaves of the chart-scheme identification are *equal*, by
`AlgebraicGeometry.Space.chartSchemeEquivalence_ringSheaf`, so the left edge contributes nothing.
Along the top and right it is `AlgebraicGeometry.Space.chartSchemeBaseChangeSharp`, the structure
map of the morphism of ringed sites attached to the morphism of schemes underlying `ψ`, followed
again by the identity.

## Main definitions

* `AlgebraicGeometry.Space.chartLocalizedSharp`: the structure map of the chart-localized base
  change, which is the bottom edge of the square.
* `AlgebraicGeometry.Space.chartSchemeBaseChangeSharp`: the structure map of base change of the
  small étale sites of the two chart schemes, which is the top edge.

## Implementation notes

Every instance is supplied explicitly, by `@`-application, rather than left to instance search.
This is not decoration.  A slice `Over W` of the small étale site of an algebraic space carries
its category instance through the type ascribed to `W`, and `W` arrives here at two spellings —
`AlgebraicGeometry.Space.SmallEtale` and `(smallEtaleRingedSite ..).C` — whose `Over`
categories are equal but not syntactically so; likewise the topology on the slice is written
both as `(SmallEtale.topology ..).over W` and as `((smallEtaleRingedSite ..).over W).J`, again
equal by `rfl` and not syntactically.  Instance search is syntactic, so a continuity datum
proved at one spelling is not found at the other, and the declarations below would be reported
as having no instance for a class whose instance is in scope.  Fixing the topologies at the
`((smallEtaleRingedSite ..).over W).J` spelling — the one the sheaves of rings of the slice
carry — and handing every continuity datum over explicitly makes the elaboration
deterministic.

For the same reason `AlgebraicGeometry.Space.isContinuous_chartSchemeBaseChange` is stated here
at all: base change of the small étale sites of schemes is continuous, by
`AlgebraicGeometry.smallEtaleBaseChange_isContinuous`, but that instance is keyed on the
topology of the scheme underlying the chart, which is not the spelling
`AlgebraicGeometry.Space.chartSchemeTopology` presents, and so it is re-registered.

## References

* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)

/-- **Base change of the small étale sites of the two chart schemes is continuous**, at the
chart spelling.  This is `AlgebraicGeometry.smallEtaleBaseChange_isContinuous`; it is restated
because that instance is keyed on the small étale topology of the scheme underlying the chart,
which is not the spelling `AlgebraicGeometry.Space.chartSchemeTopology` carries. -/
instance isContinuous_chartSchemeBaseChange :
    (chartSchemeBaseChange B S hS f hrep V).IsContinuous
      (chartSchemeTopology B S hS Y V)
      (chartSchemeTopology B S hS X (baseChangeChart B S hS f hrep V)) :=
  AlgebraicGeometry.smallEtaleBaseChange_isContinuous _ _

/-- The way round the square that goes along the top and down the right is continuous. -/
theorem isContinuous_chartSchemeBaseChangeComp :
    (chartSchemeBaseChange B S hS f hrep V ⋙
        (chartSchemeEquivalence B S hS X
          (baseChangeChart B S hS f hrep V)).functor).IsContinuous
      (chartSchemeTopology B S hS Y V)
      ((smallEtaleRingedSite B S hS X.1 X.2).over
        (baseChangeChart B S hS f hrep V)).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ (chartSchemeBaseChange B S hS f hrep V)
    (chartSchemeEquivalence B S hS X (baseChangeChart B S hS f hrep V)).functor
    (chartSchemeTopology B S hS Y V)
    (chartSchemeTopology B S hS X (baseChangeChart B S hS f hrep V))
    ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
    (isContinuous_chartSchemeBaseChange B S hS f hrep V)
    (isContinuous_chartSchemeIdentification_functor B S hS X
      (baseChangeChart B S hS f hrep V))

/-- The way round the square that goes down the left and along the bottom is continuous. -/
theorem isContinuous_chartSchemeLocalizationComp :
    ((chartSchemeEquivalence B S hS Y V).functor ⋙
        Over.post (X := V) (smallBaseChange B S hS f hrep)).IsContinuous
      (chartSchemeTopology B S hS Y V)
      ((smallEtaleRingedSite B S hS X.1 X.2).over
        (baseChangeChart B S hS f hrep V)).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ (chartSchemeEquivalence B S hS Y V).functor
    (Over.post (X := V) (smallBaseChange B S hS f hrep))
    (chartSchemeTopology B S hS Y V)
    ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
    ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
    (isContinuous_chartSchemeIdentification_functor B S hS Y V)
    (isContinuous_overPost_smallBaseChange B S hS f hrep V)

/-- **The structure map of the chart-localized base change**, the bottom edge of the square.

This is the canonical structure map of Stacks 04J0 (1) of the localization at the chart `V` of
the morphism of ringed sites attached to `f`, and it is the comparison that Stacks 04CF —
`AlgebraicGeometry.Space.over_smallBaseChangeModulePushforward_obj` — pushes the restricted
module forward along. -/
noncomputable abbrev chartLocalizedSharp :
    (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O) ⟶
      (@Functor.sheafPushforwardContinuous _ _ _ _
        (Over.post (X := V) (smallBaseChange B S hS f hrep)) RingCat.{u} _
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
        ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hrep V)).J
        (isContinuous_overPost_smallBaseChange B S hS f hrep V)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hrep V)).O) :=
  letI := isContinuous_smallBaseChange B S hS f hrep
  letI := isContinuous_overPost_smallBaseChange B S hS f hrep V
  RingedSite.MorphismLocalization.localizedStructureMap
    (smallBaseChange B S hS f hrep) (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS Y.1) V (smallEtaleRingSheaf B S hS X.1 X.2)
    (smallEtaleRingSheaf B S hS Y.1 Y.2) (smallBaseChangeSharp B S hS f hrep)

/-- **The structure map of base change of the small étale sites of the two chart schemes**, the
top edge of the square.

This is the structure map of the morphism of ringed sites of Stacks 070R (2) attached to the
morphism of schemes underlying the cartesian projection `ψ`: on an étale scheme `W` over the
chart scheme of `V` it pulls a global function back along the projection
`W ×_{V} U ⟶ W`. -/
noncomputable abbrev chartSchemeBaseChangeSharp :
    chartSchemeSiteStructureSheaf B S hS Y V ⟶
      ((chartSchemeBaseChange B S hS f hrep V).sheafPushforwardContinuous RingCat.{u}
        (chartSchemeTopology B S hS Y V)
        (chartSchemeTopology B S hS X (baseChangeChart B S hS f hrep V))).obj
        (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hrep V)) :=
  _root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
    (baseChangeChartHom B S hS f hrep V).left

end AlgebraicGeometry.Space

end
