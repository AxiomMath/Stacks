module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion

/-!
# Characterizations of open immersions

A morphism of schemes is an open immersion exactly when it is universally injective and étale,
or equivalently when it is a flat monomorphism locally of finite presentation.

## Main results

The three-way equivalence is assembled from declarations that already exist; this file only
records the Stacks tag against each of them.

* `AlgebraicGeometry.IsOpenImmersion.mono` and
  `AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme` give universal injectivity of an
  open immersion.
* `AlgebraicGeometry.Etale.instOfIsOpenImmersion` gives étaleness of an open immersion.
* `AlgebraicGeometry.Flat.instOfIsOpenImmersion` and
  `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion` give flatness and local
  finite presentation of an open immersion.
* `AlgebraicGeometry.isOpenImmersion_of_etale_universallyInjective` gives the implication from
  universal injectivity and étaleness to an open immersion.
* `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono` gives the implication from a flat
  monomorphism locally of finite presentation to an open immersion.

## Implementation notes

The declarations recorded as "(1) implies (2)" give universal injectivity and étaleness, those
recorded as "(1) implies (3)" give flatness, the monomorphism property and local finite
presentation, and the remaining two implications close the equivalence of all three conditions.
Each declaration is adopted directly rather than restated as a wrapper equivalence.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
-/

@[expose] public section

add_to_stacks 025G "(1) implies (2) and (3): monomorphism"
  AlgebraicGeometry.IsOpenImmersion.mono
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.IsOpenImmersion.mono
add_to_ega "I 2.2.3" "more general" AlgebraicGeometry.IsOpenImmersion.mono
add_to_ega "IV 17.11.5" "necessity" AlgebraicGeometry.IsOpenImmersion.mono
add_to_ega "IV 17.9.1" "(a)" AlgebraicGeometry.IsOpenImmersion.mono
add_to_ega "IV 18.10.5" "necessity" AlgebraicGeometry.IsOpenImmersion.mono
add_to_stacks 025G "(1) implies (2): universal injectivity"
  AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme
add_to_sga "3 VIB 2.6" AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme
add_to_ega "IV 17.2.6" "a) ⇒ radicial part of b)"
  AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme
add_to_stacks 025G "(1) implies (2): étale" AlgebraicGeometry.Etale.instOfIsOpenImmersion
add_to_sga "1 I 4.6" AlgebraicGeometry.Etale.instOfIsOpenImmersion
add_to_sga "1 I 5.1" "necessity" AlgebraicGeometry.Etale.instOfIsOpenImmersion
add_to_sga "1 IX 1.4" "Necessity" AlgebraicGeometry.Etale.instOfIsOpenImmersion
add_to_ega "IV 17.1.3" "more general" AlgebraicGeometry.Etale.instOfIsOpenImmersion
add_to_ega "IV 17.3.3" AlgebraicGeometry.Etale.instOfIsOpenImmersion
add_to_ega "IV 17.9.1" "(a) ⇒ étaleness in (c)" AlgebraicGeometry.Etale.instOfIsOpenImmersion
add_to_stacks 025G "(1) implies (3): flat" AlgebraicGeometry.Flat.instOfIsOpenImmersion
add_to_ega "IV 17.9.1" "(a) ⇒ flatness in (b)" AlgebraicGeometry.Flat.instOfIsOpenImmersion
add_to_ega "IV 8.1.2" "partial" AlgebraicGeometry.Flat.instOfIsOpenImmersion
add_to_stacks 025G "(1) implies (3): locally of finite presentation"
  AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion
add_to_ega "IV 1.4.3" "(i), open immersions"
  AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion
add_to_ega "IV 17.9.1" "(a)" AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion
add_to_stacks 025G "(2) implies (1)"
  AlgebraicGeometry.isOpenImmersion_of_etale_universallyInjective
add_to_stacks 025G "(3) implies (1)" AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono
add_to_sga "1 I 5.1" "special case" AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono
add_to_sga "3 X 3.7" "partial" AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono
add_to_sga "3 XXII 5.4.10" "more general" AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono
add_to_ega "IV 17.9.1" "(b) ⇒ (a)" AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono
add_to_ega "IV 17.9.2" "partial" AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono

end
