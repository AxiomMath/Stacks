module

public import StacksFrontier.AlgebraicGeometry.Groupoids.PairGroupoidDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivariantPushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent in terms of groupoids, for a morphism of schemes over a base

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of schemes over `S`, so that `Y` is a
scheme over `S` through some `g : Y ⟶ S` and `X` is a scheme over `S` through `f ≫ g`.  The
pair groupoid `(X, X ×_Y X, \mathrm{pr}_1, \mathrm{pr}_0, \mathrm{pr}_{02})` is then a groupoid
scheme over `S`, and groupoid schemes cartesian over it are the same thing as descent data
relative to `X/Y`.  That is Tag 0APF, and it is proved here.

## Main results

* `AlgebraicGeometry.cartesianOverPairGroupoidEquivDescentDatum`: **Tag 0APF**, general case.

The case `Y = S` is `AlgebraicGeometry.cartesianOverEquivDescentDatum`, proved in
`StacksFrontier.AlgebraicGeometry.Groupoids.PairGroupoidDescent` and tagged there.  It is not an
instance of the general statement up to definitional equality, because
`CategoryTheory.Over.map (𝟙 S)` is not the identity functor, so the two statements are
separate declarations and both carry the tag.

## Implementation notes

The statement is assembled from two independent halves.
`AlgebraicGeometry.cartesianOverEquivDescentDatum` is the case where the base scheme of the
groupoid is the target of `f`; it is the one whose arrow scheme is literally the binary product
formed in `CategoryTheory.Over Y`, which is what the descent datum's gluing isomorphism is
built out of.  `AlgebraicGeometry.cartesianOverPushforwardEquivalence` moves the base scheme of
a groupoid forward along `g`, which is legitimate because the scheme of composable arrows is a
*pullback* and `CategoryTheory.Over.map g` preserves pullbacks; it does not preserve binary
products, which is why the comparison with descent data is kept entirely over `Y` and only the
groupoid is pushed forward.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 0APD](https://stacks.math.columbia.edu/tag/0APD)
* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
* [Stacks Project, Tag 0APF](https://stacks.math.columbia.edu/tag/0APF)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- **Tag 0APF.**  Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of schemes over `S`,
the structure morphism of `Y` being `g : Y ⟶ S`.  Groupoid schemes over `S` cartesian over the
pair groupoid `(X, X ×_Y X, \mathrm{pr}_1, \mathrm{pr}_0, \mathrm{pr}_{02})` are the same thing
as descent data relative to `X/Y`. -/
@[stacks 0APF "the equivalence for a morphism of schemes over a base `S`, the general case"]
def cartesianOverPairGroupoidEquivDescentDatum {S Y X : Scheme.{u}} (g : Y ⟶ S) (f : X ⟶ Y) :
    CartesianOver ((pairGroupoid f).pushforward g) ≌ DescentDatum f :=
  (cartesianOverPushforwardEquivalence g (pairGroupoid f)).symm.trans
    (cartesianOverEquivDescentDatum f)

end AlgebraicGeometry

end

end
