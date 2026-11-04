module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.LiftedEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.IntegralUniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.Thickening


/-!
# Essential surjectivity of base change on spaces-étale sites

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. Base change
`V ↦ X ×_Y V` from the spaces-étale site of `Y` to that of `X` is essentially surjective as
soon as every object of the spaces-étale site of `X` admits a *lifted étale presentation*: an
étale equivalence relation of objects of the big fppf site étale over `Y` whose base change
along `f` is an étale chart of the given object, together with the kernel pair of that chart.
Every object admits one when `f` is a surjective closed immersion (the inclusion of a
thickening of arbitrary order), and more generally when `f` is integral, universally injective
and surjective. Together with full faithfulness, base change is then an equivalence of
spaces-étale sites.

All names below are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `LiftedEtalePresentation`: the lifted-presentation datum.

## Main results

* `mem_essImage_spacesBaseChange_of_liftedEtalePresentation`: for an arbitrary `f`, an object
  with a lifted étale presentation is in the essential image of base change along `f`.
* `nonempty_liftedEtalePresentation_of_isClosedImmersion_of_isSurjective`,
  `nonempty_liftedEtalePresentation_of_isThickening`, `nonempty_liftedEtalePresentation` and
  `nonempty_liftedEtalePresentation_of_isIntegralHom_of_universallyInjective`: every object of
  the spaces-étale site admits a lifted étale presentation across a surjective closed
  immersion, the inclusion of a thickening, the inclusion of a first-order thickening, and an
  integral, universally injective and surjective morphism respectively.
* `essSurj_spacesBaseChange_of_isClosedImmersion_of_isSurjective` and
  `isEquivalence_spacesBaseChange_of_isClosedImmersion_of_isSurjective`: base change along a
  surjective closed immersion is essentially surjective, and an equivalence.
* `essSurj_spacesBaseChange_of_isThickening` and
  `isEquivalence_spacesBaseChange_of_isThickening`: the same along the inclusion of a
  thickening of arbitrary order.
* `essSurj_spacesBaseChange_of_isFirstOrderThickening` and
  `isEquivalence_spacesBaseChange_of_isFirstOrderThickening`: the same along the inclusion of a
  first-order thickening.
* `essSurj_spacesBaseChange_of_isIntegralHom_of_universallyInjective` and
  `isEquivalence_spacesBaseChange_of_isIntegralHom_of_universallyInjective`: the same along an
  integral, universally injective and surjective morphism.
* `existsUnique_hom_presheaf_of_isIntegralHom_of_universallyInjective`: a morphism into an
  algebraic space étale over `Y` extends uniquely across a base change of an integral,
  universally injective and surjective morphism.
* `existsUnique_hom_presheaf_of_isFirstOrderThickening`: a morphism into a formally étale
  algebraic space extends uniquely across a base change of the inclusion of a first-order
  thickening.
* `exists_hom_presheaf_of_isThickening` and `hom_ext_presheaf_of_isThickening`: existence and
  uniqueness of such extensions across a base change of the inclusion of a thickening.
* `exists_isPullback_of_iso_pullback_toScheme` and
  `exists_isPullback_presheaf_of_iso_pullback_toScheme`: a cartesian square of schemes between
  objects of the site is one of the site, and, pasted onto a chart of the base, one of
  presheaves over the base.
* `exists_chart_isClosedImmersion_of_isClosedImmersion_of_isSurjective`: a surjective closed
  immersion restricts to a closed immersion of objects of the site, surjective on points, over
  any chart of the target.
* `exists_chart_universalHomeomorphism_of_isIntegralHom_of_universallyInjective`: an integral,
  universally injective and surjective morphism restricts to a universal homeomorphism of
  schemes over any chart of the target.
* `exists_etaleLift_isPullback_of_chart`: an étale scheme over the restriction of a surjective
  closed immersion to a chart lifts, cartesianly, to an object of the site étale over the chart.
* `exists_liftedEtalePresentation_charts_of_isClosedImmersion_of_isSurjective`: the charts, the
  kernel pair and the two étale lifts of a lifted étale presentation exist.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 0616](https://stacks.math.columbia.edu/tag/0616)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/
