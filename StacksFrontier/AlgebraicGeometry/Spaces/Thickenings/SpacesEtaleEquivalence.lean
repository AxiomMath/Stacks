module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj

/-!
# The étale site of a thickening of algebraic spaces

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, of arbitrary order. Base
change along the inclusion, `V ↦ G ×_X V`, is an *equivalence of categories* from the
spaces-étale site of the ambient space `X` to the spaces-étale site of the closed subspace `G`
— this is the identification of Stacks 05ZL — and at a *first-order* thickening it is moreover
*fully faithful* on the small étale sites of étale scheme charts.

In the notation of the source, `G` is `X` and `X` is `X'`, so the functor is the one the source
writes `V' ↦ V = X ×_{X'} V'` and it runs `X'_étale → X_étale`.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsThickening`: **Stacks 05ZL**, the
  equivalence of spaces-étale sites at a thickening of arbitrary order, as a
  `CategoryTheory.Equivalence`.
* `AlgebraicGeometry.Space.isFirstOrderThickening_range_inclusion`: the range of the inclusion
  of a thickening, read as a morphism of algebraic spaces, is the closed subspace itself, so
  the first-order hypothesis transports to the form in which Stacks 05ZH is stated.
* `AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening`: the same
  equivalence at a first-order thickening.
* `AlgebraicGeometry.Space.isPullback_spacesEtaleEquivalenceOfIsFirstOrderThickening`: the
  value of its functor at `V` sits in the cartesian square identifying it with the fibre
  product `G ×_X V`, which is the description of the functor in the source.
* `AlgebraicGeometry.Space.fullyFaithfulThickeningChartBaseChangeOfIsFirstOrderThickening`:
  base change of étale *scheme charts* along the inclusion is fully faithful, that is, the
  functor `X'_étale → X_étale` of the source is fully faithful.

## Implementation notes

Both halves of the spaces-étale equivalence are available at a thickening of arbitrary order:
full faithfulness is
`AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsIntegralHomOfUniversallyInjective`,
since the inclusion of a thickening is integral, universally injective and surjective, and
essential surjectivity is
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isClosedImmersion_of_isSurjective`; the
two are combined into
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isClosedImmersion_of_isSurjective`.
What is added here is the hypothesis shape of this tag, the equivalence as an object, and the
passage to scheme charts.

The library form of Stacks 05ZH is stated for a morphism `f` of algebraic spaces which is a
monomorphism and whose range is a first-order thickening of the target. A thickening in the sense
of Stacks 05ZK is instead a *subfunctor* `G` of the ambient space, so its inclusion is the
canonical `G.ι`, which is a monomorphism outright, and whose range is `G` itself by
`CategoryTheory.Subfunctor.range_ι`. Rewriting along that equality is the whole of
`AlgebraicGeometry.Space.isFirstOrderThickening_range_inclusion`.

The cartesian square is not re-proved: it is the `isPullback` field of
`AlgebraicGeometry.Space.spacesBaseChange`, the Stacks 03G2 base-change datum, read at the
functor of the equivalence through
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening_functor`.

Full faithfulness on scheme charts needs no new geometry. Chart base change becomes
spaces-étale base change after the Stacks 03G1 comparison, by
`AlgebraicGeometry.Space.smallBaseChange_comparison`, and the comparison is fully faithful
(`AlgebraicGeometry.Space.comparisonFunctor_full`,
`AlgebraicGeometry.Space.comparisonFunctor_faithful`) because `yoneda` is. So the composite of
chart base change with the comparison at `G` is fully faithful, being isomorphic to a
composite of fully faithful functors, and cancelling the faithful comparison at `G` leaves
chart base change fully faithful.

## What is not covered

The source states Stacks 05ZS for a thickening of *arbitrary* order, and as an *equivalence* of
the small étale sites of schemes étale over the two spaces. The first is reached, on the
spaces-étale site; the second is not.

*Arbitrary order.* On the spaces-étale site the equivalence holds at a thickening of arbitrary
order, `AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsThickening` (Stacks 05ZL). It is not
obtained by induction on the order — the defining ideal of a thickening need not be nilpotent,
so a thickening is not in general a finite chain of first-order ones — but directly: full
faithfulness holds for every integral, universally injective and surjective morphism, and the
inclusion of a thickening is one by
`AlgebraicGeometry.Space.isIntegralHom_universallyInjective_isSurjective_ι_of_isThickening`,
while essential surjectivity needs only that the inclusion restricts on charts to a surjective
closed immersion of schemes, which is what Stacks 039R takes. What is still restricted to first
order is the *chart-level* full faithfulness below, which is stated through the first-order
form of Stacks 05ZH.

*Essential surjectivity on scheme charts.* Upgrading the chart-level full faithfulness above
to an equivalence is the content of Stacks 07VW, and it needs that `V` is a scheme exactly
when `G ×_X V` is. The elementary direction is
`AlgebraicGeometry.Space.isRepresentable_of_isThickening`; the converse is Stacks 05ZR, whose
library form
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_thickening` rests on three inputs
of Stacks 07VT that this library does not prove, so no essential surjectivity on
`AlgebraicGeometry.Space.SmallEtale` is claimed.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- The inclusion of a thickening `G ⊂ X`, read as a morphism of algebraic spaces over `S`, is
a monomorphism: it is the canonical inclusion `G.ι` of a subfunctor. -/
theorem mono_hom_inclusion (hG : IsThickening B S hS X G) :
    Mono (IsThickening.inclusion B S hS hG).hom :=
  inferInstanceAs (Mono G.ι)

/-- The range of the inclusion of a first-order thickening `G ⊂ X` is `G` itself, so `G ⊂ X`
being a first-order thickening is the same as the range of the inclusion being one.

This is the hypothesis shape in which Stacks 05ZH,
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening`, is
stated. -/
theorem isFirstOrderThickening_range_inclusion
    (hG : IsFirstOrderThickening B S hS X G) :
    IsFirstOrderThickening B S hS X
      (Subfunctor.range (IsThickening.inclusion B S hS (hG.isThickening B S hS)).hom) := by
  have hrange : Subfunctor.range
      (IsThickening.inclusion B S hS (hG.isThickening B S hS)).hom = G :=
    Subfunctor.range_ι G
  rw [hrange]
  exact hG

/-! ### The equivalence of spaces-étale sites -/

/-- Let `G ⊂ X` be a thickening of algebraic spaces over `S`, of arbitrary order. Base change
along the inclusion, `V ↦ G ×_X V`, is an equivalence of categories from the spaces-étale site of
the ambient space `X` to the spaces-étale site of the closed subspace `G`. -/
@[stacks 05ZL "the identification of the two spaces-étale sites of Stacks 03G0, as an \
equivalence of categories, for a thickening of arbitrary order"]
noncomputable def spacesEtaleEquivalenceOfIsThickening (hG : IsThickening B S hS X G) :
    SpacesEtale B S hS X ≌ SpacesEtale B S hS (IsThickening.space B S hS hG) :=
  letI := isEquivalence_spacesBaseChange_of_isClosedImmersion_of_isSurjective B S hS
    (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG)
    (isSurjective_ι_of_isThickening B S hS hG)
  (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.asEquivalence

/-- **Stacks 05ZS at a first-order thickening, on the spaces-étale site.** Let `G ⊂ X` be a
first-order thickening of algebraic spaces over `S`. Base change along the inclusion,
`V ↦ G ×_X V`, is an equivalence of categories from the spaces-étale site of `X` to the
spaces-étale site of `G`.

In the notation of the source, `G` is `X` and `X` is `X'`: the functor is `V' ↦ X ×_{X'} V'`
and the equivalence runs `X'_étale → X_étale`.

The functor is the one of the Stacks 03G2 base-change datum
`AlgebraicGeometry.Space.spacesBaseChange`, and it is an equivalence because a first-order
thickening is in particular a thickening: this is
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsThickening`, the arbitrary-order
equivalence of Stacks 05ZL, read at first order. -/
@[stacks 05ZS "the FIRST-ORDER thickening case, on the spaces-étale site of Stacks 03G0. The \
source states the tag for a thickening of arbitrary order and as an equivalence of the small \
étale sites of scheme charts; on the spaces-étale site the arbitrary-order equivalence is \
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsThickening`, and on the small étale sites \
of scheme charts this module covers the full faithfulness of the functor, by \
`AlgebraicGeometry.Space.fullyFaithfulThickeningChartBaseChangeOfIsFirstOrderThickening`. The \
module's `What is not covered` section sets out the differences from the source"]
noncomputable def spacesEtaleEquivalenceOfIsFirstOrderThickening
    (hG : IsFirstOrderThickening B S hS X G) :
    SpacesEtale B S hS X ≌
      SpacesEtale B S hS (IsThickening.space B S hS (hG.isThickening B S hS)) :=
  spacesEtaleEquivalenceOfIsThickening B S hS (hG.isThickening B S hS)

/-- The functor of the equivalence of
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening` is base change along
the inclusion of the thickening. -/
theorem spacesEtaleEquivalenceOfIsFirstOrderThickening_functor
    (hG : IsFirstOrderThickening B S hS X G) :
    (spacesEtaleEquivalenceOfIsFirstOrderThickening B S hS hG).functor =
      (spacesBaseChange B S hS
        (IsThickening.inclusion B S hS (hG.isThickening B S hS))).functor :=
  rfl

/-- The value at `V` of the functor of
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening` is the fibre product
`G ×_X V`: the cartesian projection to `V` and the structure morphism to `G` form a cartesian
square over the inclusion of the thickening.

This is the description of the functor in the source, `V' ↦ V = X ×_{X'} V'`. -/
theorem isPullback_spacesEtaleEquivalenceOfIsFirstOrderThickening
    (hG : IsFirstOrderThickening B S hS X G) (V : SpacesEtale B S hS X) :
    IsPullback
      ((spacesBaseChange B S hS
        (IsThickening.inclusion B S hS (hG.isThickening B S hS))).projection.app V)
      (((spacesEtaleEquivalenceOfIsFirstOrderThickening B S hS hG).functor.obj V)).1.hom
      V.1.hom (IsThickening.inclusion B S hS (hG.isThickening B S hS)) :=
  (spacesBaseChange B S hS
    (IsThickening.inclusion B S hS (hG.isThickening B S hS))).isPullback V

/-! ### Full faithfulness on the small étale sites of scheme charts -/

/-- **Stacks 05ZS, full faithfulness of the functor `X'_étale → X_étale`, at a first-order
thickening.** Let `G ⊂ X` be a first-order thickening of algebraic spaces over `S`. Base
change of étale *scheme* charts along the inclusion,
`AlgebraicGeometry.Space.thickeningChartBaseChange`, is fully faithful.

This is on the source's own site: the objects are the schemes étale over the two spaces. Only
full faithfulness is reached. Essential surjectivity is Stacks 07VW, which rests on
Stacks 05ZR; these are `AlgebraicGeometry.Space.smallEtalePullback_isEquivalence` and
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_thickening`, and they do not apply
here, for two separate reasons, as the module's `What is not covered` section sets out: each
carries three inputs of Stacks 07VT that this library does not prove, and the 07VW equivalence
is for `AlgebraicGeometry.Space.smallEtalePullback`, which nothing in this library relates as a
functor to `AlgebraicGeometry.Space.thickeningChartBaseChange`.

Chart base change becomes spaces-étale base change after the Stacks 03G1 comparison, by
`AlgebraicGeometry.Space.smallBaseChange_comparison`. The comparison is fully faithful and
spaces-étale base change at a first-order thickening is fully faithful, so the composite of
chart base change with the comparison at `G` is isomorphic to a fully faithful functor, hence
fully faithful; cancelling the faithful comparison at `G` leaves chart base change fully
faithful. -/
@[stacks 05ZS "FULL FAITHFULNESS ONLY, at a FIRST-ORDER thickening, of the source's own \
functor `X'_étale → X_étale` on the small étale sites of SCHEME charts, Stacks 03ED. The \
source asserts an equivalence, so essential surjectivity on those sites is a separate \
statement, Stacks 07VW. The restriction to first order is inherited from the library's \
Stacks 05ZH, `AlgebraicGeometry.Space.full_spacesBaseChange_of_isFirstOrderThickening` and \
`AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isFirstOrderThickening`. The companion \
statement on the spaces-étale site of Stacks 03G0, where the full equivalence IS available at \
first order, is \
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening`; the module's `What \
is not covered` section sets out the differences from the source"]
noncomputable def fullyFaithfulThickeningChartBaseChangeOfIsFirstOrderThickening
    (hG : IsFirstOrderThickening B S hS X G) :
    (thickeningChartBaseChange B S hS (hG.isThickening B S hS)).FullyFaithful :=
  letI := mono_hom_inclusion B S hS (hG.isThickening B S hS)
  letI := full_spacesBaseChange_of_isFirstOrderThickening B S hS
    (IsThickening.inclusion B S hS (hG.isThickening B S hS))
    (isFirstOrderThickening_range_inclusion B S hS hG)
  letI := faithful_spacesBaseChange_of_isFirstOrderThickening B S hS
    (IsThickening.inclusion B S hS (hG.isThickening B S hS))
    (isFirstOrderThickening_range_inclusion B S hS hG)
  letI := comparisonFunctor_full B S hS X
  letI := comparisonFunctor_faithful B S hS X
  letI := comparisonFunctor_full B S hS (IsThickening.space B S hS (hG.isThickening B S hS))
  letI :=
    comparisonFunctor_faithful B S hS (IsThickening.space B S hS (hG.isThickening B S hS))
  letI := Functor.Full.of_comp_faithful_iso (smallBaseChange_comparison B S hS
    (IsThickening.inclusion B S hS (hG.isThickening B S hS))
    (isClosedImmersion_inclusion_of_isThickening B S hS (hG.isThickening B S hS)).rep)
  letI := Functor.Faithful.of_comp_iso (smallBaseChange_comparison B S hS
    (IsThickening.inclusion B S hS (hG.isThickening B S hS))
    (isClosedImmersion_inclusion_of_isThickening B S hS (hG.isThickening B S hS)).rep)
  Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry.Space

end
