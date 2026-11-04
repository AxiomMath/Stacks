module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts

/-!
# Compatible étale charts for a fibre product of algebraic spaces

Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of algebraic spaces over a scheme `S`. Choosing
a surjective étale chart `v : yoneda.obj V ⟶ Y` of the target and then surjective étale charts
`a` and `b` of the two base changes `V ×_Y X` and `V ×_Y Y'`, one obtains charts of `X` and of
`Y'` lying over `v`, hence morphisms `p : U ⟶ V` and `q : V' ⟶ V` of the big fppf site of `S`.
The fourth corner of the square can then be charted by the fibre product `U ×_V V'` *of
schemes*: the induced chart

```
yoneda.obj (U ×_V V') ⟶ X ×_Y Y'
```

is again surjective and étale, and it is compatible with `a` and `b` in the sense that its two
components are the two projections of `U ×_V V'` followed by `a` and `b`. So a cartesian square
of algebraic spaces has a presentation by a cartesian square of schemes.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_compatible_etale_charts` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts`: the four objects of the
  site, the cartesian square they form after passing to schemes, the compatible surjective étale
  charts of the four algebraic spaces, and the equations identifying the chart of the fibre
  product with the one assembled from the other three.

## Implementation notes

The fourth algebraic space is the chosen presheaf fibre product `pullback f g`, which is an
algebraic space by `AlgebraicGeometry.isAlgebraicSpace_pullback`; the two base changes used to
chart `X` and `Y'` are algebraic spaces for the same reason, the representable `yoneda.obj V`
being one by `AlgebraicGeometry.isAlgebraicSpace_yoneda`. Surjectivity and étaleness of a chart
are the relatively representable properties `CategoryTheory.MorphismProperty.presheaf` of the
inverse images of `AlgebraicGeometry.Surjective` and `AlgebraicGeometry.Etale` along
`AlgebraicGeometry.BigFppfOver.toScheme`, exactly as in the definition of an algebraic space;
the stability of those inverse images under base change and composition is
`AlgebraicGeometry.Space.inverseImage_isStableUnderBaseChange` and
`AlgebraicGeometry.Space.inverseImage_isStableUnderComposition`.

Cartesianity of the square of charts is asserted after applying
`AlgebraicGeometry.BigFppfOver.toScheme`, i.e. for the underlying schemes; it holds because that
functor preserves fibre products
(`AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme`).

The chart `c` of `X ×_Y Y'` is shown surjective and étale by factoring it as
`U ×_V V' ⟶ W ⟶ X ×_Y Y'`, where `W := (X ×_Y Y') ×_{Y'} yoneda.obj V'`. The second factor is a
base change of `b` composed with a base change of `v`, and the first factor is a base change of
`a`: the auxiliary square exhibiting `W ⟶ V ×_Y X` as the base change of `yoneda.map q` along
the first projection is obtained from the two pastings
`W = ((X ×_Y Y') ×_{Y'} V') = X ×_Y V'` and `(V ×_Y X) ×_V V' = X ×_Y V'`, which is why no
explicit universal property has to be verified by hand.

## References

* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

end AlgebraicGeometry.Space

end
