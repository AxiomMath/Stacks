module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FppfLocalTarget

/-!
# Cohen–Macaulayness with locally Noetherian fibres as a morphism property

`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay` takes the locally Noetherian fibre witness as
an explicit argument. Bundling that witness existentially gives the morphism property
`AlgebraicGeometry.cohenMacaulayWithLocallyNoetherianFibers`, and this property respects
isomorphisms: `AlgebraicGeometry.cohenMacaulayWithLocallyNoetherianFibers_respectsIso`.

## References

* [Stacks Project, Tag 045R](https://stacks.math.columbia.edu/tag/045R)
-/
