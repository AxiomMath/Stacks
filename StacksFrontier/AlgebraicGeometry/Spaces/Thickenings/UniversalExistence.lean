module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.FirstOrderClauseAndAffineSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.SiteThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.AmbientSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.ChartRelationLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.Construction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.ExistenceAndTransport

/-!
# Existence of the universal first order thickening of a formally unramified morphism

A formally unramified morphism `h : Z ⟶ X` of algebraic spaces over `S` has a universal first
order thickening `Z ⊂ Z'` of `Z` over `X` in the sense of Stacks 0602. The thickening is built
from an étale chart `V ⟶ Z` of the source lying over a chart `U ⟶ X` of the target: the
scheme-level universal first order thickening `V ⊂ V'` of Stacks 04F3 is transported to the
site, the étale equivalence relation presenting `Z` is lifted to an étale equivalence relation
`R'` on `V'`, and the ambient space `Z'` is the quotient `V'/R'`.

## Main results

* `AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`: **Stacks 0606**, the
  existence of the thickening, carrying nothing.
* `isClosedSubspace_and_isFirstOrderThickening_of_surjectiveEtaleChart`, of the namespace
  `Stacks.Spaces.UniversalThickening`: **Stacks 0BPI, the first-order clause**, for a one-member
  covering by a surjective étale scheme chart and a subfunctor which is a sheaf, which is the
  form this construction consumes it in and so no longer carried.
* `Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening`: Stacks 05ZH for
  the spaces-étale site in the form this construction consumes it, repackaged from the
  equivalence of sites and so no longer carried.
* `Stacks.Spaces.UniversalThickening.exists_site_universalFirstOrderThickening`: a morphism of
  the site whose underlying morphism of schemes is formally unramified has a universal
  first-order thickening of schemes inside the site.

## Implementation notes

The conclusion is `Nonempty` of the library's Stacks 0607 datum
`AlgebraicGeometry.Space.UniversalFirstOrderThickening`, whose `isUniversal` field is the
unique-extension clause of Stacks 0602; the uniqueness the source's definite article refers to
is therefore proved rather than asserted, and no thickening is chosen out of an existence
statement.

A first-order clause of Stacks 0BPI used to be carried as a hypothesis, to descend the
thickening `Y ⊂ Z'` along the étale chart `V' ⟶ Z'`. It no longer is.
`isClosedSubspace_and_isFirstOrderThickening_of_surjectiveEtaleChart` below proves it for the
one-member covering by a surjective étale scheme chart that is all this construction uses. Its
three ingredients are Stacks 03I2 at the closed immersions, whose effective-descent input
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion` is outright;
surjectivity on points of the chart and of the base change; and
`definingIdealAt_pow_eq_bot_of_surjectiveEtaleChart`, which descends the vanishing of the
square of the defining ideal from the charts of `V'` to the charts of `Z'` along the base
change of a chart. It asks of `Y` the fppf sheaf condition, which
the fpqc statement of the source does not; here `Y` is a sheafification and so satisfies it.
The library's only other `@[stacks 0BPI]` carrier,
`AlgebraicGeometry.Space.thickening_isLocalAtTarget_fpqc`, proves the order-free clause for an
arbitrary fpqc covering, and its module records the first-order clause as absent there.

A Stacks 05ZH input used to be carried alongside it, to see that the comparison morphism
between two universal first order thickenings is étale and cartesian. It no longer is.
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEssSurj.lean` proves essential
surjectivity of spaces-étale base change for a monomorphism whose range is a first-order
thickening, and `Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening` below
reads the required cartesian square off it; the monomorphism hypothesis costs nothing here,
since the morphism applied to is the inclusion of a subfunctor. Three declarations carry
`@[stacks 05ZH]` for that first-order thickening case — full faithfulness in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleFullyFaithful.lean` and essential
surjectivity together with the resulting equivalence in `SpacesEtaleEssSurj.lean` — which is
all this construction needs. The source's wider class of integral, universally injective and
surjective morphisms is reached by full faithfulness, in
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleFaithful.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleFull.lean`, but not by essential
surjectivity, so the equivalence this construction consumes is available for the first-order
case only.

Stacks 06AD is used through `Stacks.Thickenings.isAffine_of_isFirstOrderThickening`, which is
unconditional, so the surjectivity hypothesis of the other 06AD carrier is not needed. Stacks
03MB and 03G8 are not used: the defining ideal of the thickening of a scheme chart is read off
by `AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map`.

## References

* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 0BPI](https://stacks.math.columbia.edu/tag/0BPI)
-/
