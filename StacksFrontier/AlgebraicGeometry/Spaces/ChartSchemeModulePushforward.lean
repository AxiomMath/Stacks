module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeBaseChangeRingSquare

/-!
# The direct image of modules across the chart base-change square

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`, let `V` be an
étale scheme chart of `Y` and let `U = V ×_Y X` be the base-changed chart of `X`, with
`ψ : U ⟶ V` the cartesian projection.  Pushing an `𝒪_X`-module on the slice at `U` forward along
the localization at `V` of base change of charts, and then reading the result on the small étale
site of the chart scheme of `V`, is reading the module on the small étale site of the chart scheme
of `U` and then pushing it forward along `ψ`.

This is the square of ringed sites of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeBaseChangeRingSquare.lean` carried to sheaves of
modules: the two composite direct images are the direct images along the two composite routes,
because direct image is compatible with composition of morphisms of ringed sites, and those two
routes agree by `AlgebraicGeometry.Space.chartSchemeBaseChangeSharp_square`.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeSiteModulePushforwardIso`: **the identification of the two
  direct images**, at one module.

## Implementation notes

Every instance is supplied explicitly, by `@`-application.  This is not decoration: the chart
arrives at the two spellings `AlgebraicGeometry.Space.SmallEtale` and
`(smallEtaleRingedSite ..).C`, and the topology of a slice at the two spellings
`(SmallEtale.topology ..).over V` and `((smallEtaleRingedSite ..).over V).J`; each pair is equal
by `rfl` and not syntactically, so a continuity datum proved at one spelling is not found by
instance search at the other, and the declaration below would be reported as having no instance
for a class whose instance is in scope.

For the same reason the composite is written out with
`CategoryTheory.SheafOfModules.pushforwardComp` at both ends rather than left to unfolding: that
isomorphism is `CategoryTheory.Iso.refl`, so the two readings of each end are definitionally
equal, but the definitional check runs through
`CategoryTheory.Functor.sheafPushforwardContinuous` and costs more than the heartbeat budget.

## References

* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hrep : yoneda.relativelyRepresentable f.hom)
  (V : SmallEtale B S hS Y.1)

/-- **The direct image of modules across the chart base-change square**, at one module.
Pushing an `𝒪_X`-module on the slice at the base-changed chart `U` forward along the localization
at `V` of base change of charts, and reading the result on the small étale site of the chart
scheme of `V`, is reading it on the small étale site of the chart scheme of `U` and pushing it
forward along the morphism of schemes underlying the cartesian projection `ψ`.

Both sides are the direct image along one of the two composite routes round the square of ringed
sites, by `CategoryTheory.SheafOfModules.pushforwardComp`, and the two routes agree by
`AlgebraicGeometry.Space.chartSchemeBaseChangeSharp_square`. -/
noncomputable def chartSchemeSiteModulePushforwardIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSite B S hS X.1 X.2).over
        (baseChangeChart B S hS f hrep V)).O)) :
    chartSchemeSiteModule B S hS Y V
        ((@SheafOfModules.pushforward
          ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).C _
          ((smallEtaleRingedSite B S hS X.1 X.2).over
            (baseChangeChart B S hS f hrep V)).C _
          ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
          ((smallEtaleRingedSite B S hS X.1 X.2).over
            (baseChangeChart B S hS f hrep V)).J
          (Over.post (X := V) (smallBaseChange B S hS f hrep))
          (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O)
          (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
            (baseChangeChart B S hS f hrep V)).O)
          (isContinuous_overPost_smallBaseChange B S hS f hrep V)
          (chartLocalizedSharp B S hS f hrep V)).obj M) ≅
      (@SheafOfModules.pushforward
        (chartSchemeSite B S hS Y V) _
        (chartSchemeSite B S hS X (baseChangeChart B S hS f hrep V)) _
        (chartSchemeTopology B S hS Y V)
        (chartSchemeTopology B S hS X (baseChangeChart B S hS f hrep V))
        (chartSchemeBaseChange B S hS f hrep V)
        (chartSchemeSiteStructureSheaf B S hS Y V)
        (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hrep V))
        (isContinuous_chartSchemeBaseChange B S hS f hrep V)
        (chartSchemeBaseChangeSharp B S hS f hrep V)).obj
        (chartSchemeSiteModule B S hS X (baseChangeChart B S hS f hrep V) M) :=
  (@SheafOfModules.pushforwardComp.{u}
      (chartSchemeSite B S hS Y V) _
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).C _
      ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
      (chartSchemeTopology B S hS Y V)
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
      (chartSchemeEquivalence B S hS Y V).functor
      (chartSchemeSiteStructureSheaf B S hS Y V)
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O)
      (isContinuous_chartSchemeIdentification_functor B S hS Y V)
      (chartSchemeEquivSharp B S hS Y V)
      ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
      (Over.post (X := V) (smallBaseChange B S hS f hrep))
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).O)
      (isContinuous_overPost_smallBaseChange B S hS f hrep V)
      (chartLocalizedSharp B S hS f hrep V)).app M ≪≫
  (@SheafOfModules.pushforwardCongr₂.{u}
    (chartSchemeSite B S hS Y V) _
    ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
    (chartSchemeTopology B S hS Y V)
    ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
    ((chartSchemeEquivalence B S hS Y V).functor ⋙
      Over.post (X := V) (smallBaseChange B S hS f hrep))
    (chartSchemeBaseChange B S hS f hrep V ⋙
      (chartSchemeEquivalence B S hS X (baseChangeChart B S hS f hrep V)).functor)
    (chartSchemeSiteStructureSheaf B S hS Y V)
    (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).O)
    (isContinuous_chartSchemeLocalizationComp B S hS f hrep V)
    (isContinuous_chartSchemeBaseChangeComp B S hS f hrep V)
    _ _
    (chartSchemeEquivalenceBaseChangeIso B S hS f hrep V)
    (chartSchemeBaseChangeSharp_square B S hS f hrep V)).symm.app M ≪≫
    ((@SheafOfModules.pushforwardComp.{u}
      (chartSchemeSite B S hS Y V) _
      (chartSchemeSite B S hS X (baseChangeChart B S hS f hrep V)) _
      ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
      (chartSchemeTopology B S hS Y V)
      (chartSchemeTopology B S hS X (baseChangeChart B S hS f hrep V))
      (chartSchemeBaseChange B S hS f hrep V)
      (chartSchemeSiteStructureSheaf B S hS Y V)
      (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hrep V))
      (isContinuous_chartSchemeBaseChange B S hS f hrep V)
      (chartSchemeBaseChangeSharp B S hS f hrep V)
      ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
      (chartSchemeEquivalence B S hS X (baseChangeChart B S hS f hrep V)).functor
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).O)
      (isContinuous_chartSchemeIdentification_functor B S hS X
        (baseChangeChart B S hS f hrep V))
      (chartSchemeEquivSharp B S hS X (baseChangeChart B S hS f hrep V))).app M).symm


end AlgebraicGeometry.Space

end
