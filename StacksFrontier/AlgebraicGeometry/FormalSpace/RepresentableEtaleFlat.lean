module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism

/-!
# Representable étale morphisms are flat

Let `S` be a scheme contained in a big fppf site `B`. A morphism of fppf sheaves over `S` which
is representable by algebraic spaces inherits the theory of morphisms of algebraic spaces; in
particular a representable étale morphism is flat, that is satisfies the every-étale-chart
condition of **Stacks 03MJ** for flatness of morphisms of schemes after every represented base
change.

This is the companion of
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isRepresentableEtale`, and it is what
makes `AlgebraicGeometry.FormalSpace.IsRepresentableFlat` the conclusion of something: the five
transfer lemmas of **Stacks 0AKS**, **Stacks 0GXR**, **Stacks 0GXS**, **Stacks 0AKT** and
**Stacks 0AKW** apply to a surjective flat morphism, while the morphisms the proofs of
**Stacks 0AKX** and **Stacks 0AQD** produce are surjective and étale.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_flat_of_isEtaleULift_of_uliftYoneda`: an
  étale morphism of presheaves whose target is a universe-lifted Yoneda presheaf is flat on
  every étale chart.
* `AlgebraicGeometry.FormalSpace.IsRepresentableFlat.of_isRepresentableEtale`: a morphism of
  fppf sheaves which is representable by algebraic spaces and étale is representable flat.

## Implementation notes

The argument is the one
`AlgebraicGeometry.Space.isLocallyOfFiniteTypeULift_of_isEtaleULift_of_uliftYoneda` makes for
being locally of finite type, with the last step changed: in a commuting square of étale charts
over a morphism `h` of the site, the chart of the target and the composite of the chart of the
source with the morphism are both étale on schemes, so étale cancellation of **Stacks 02GW**
leaves `h` étale, and an étale morphism of schemes is smooth and hence flat.

## References

* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 0AJG](https://stacks.math.columbia.edu/tag/0AJG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves on the big fppf site of `S` which is étale in the sense of
**Stacks 03FR** and whose target is a universe-lifted Yoneda presheaf is flat on every étale
chart in the sense of **Stacks 03MJ**: in a commuting square of étale charts over a morphism `h`
of the site, the chart of the target and the composite of the chart of the source with the
morphism are both étale on schemes, so `h` is étale and a fortiori flat. -/
alias holdsOnEveryEtaleChartULift_flat_of_isEtaleULift_of_uliftYoneda :=
  flat_holdsOnEveryEtaleChartULift_of_isEtaleULift_of_uliftYoneda

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of fppf sheaves on the big fppf site of `S` which is representable by algebraic
spaces and étale is representable flat: the morphism of algebraic spaces cut out by a
represented base change is étale, hence flat on every étale chart. -/
alias IsRepresentableFlat.of_isRepresentableEtale := isRepresentableFlat_of_isRepresentableEtale

end AlgebraicGeometry.FormalSpace

end
