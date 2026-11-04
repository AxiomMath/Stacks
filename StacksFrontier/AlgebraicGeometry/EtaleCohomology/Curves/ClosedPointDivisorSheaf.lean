module

public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits

/-!
# The sheaf `⨁_x i_{x,*} ℤ` over the closed points of a scheme

The divisor sequence of Stacks 03RM on a curve `X`,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0`,
has as its third term the coproduct of the skyscraper sheaves
`Stacks.EtaleCohomology.integerSkyscraper` over the closed points of `X`. The summands are
constructed in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDirectImage`;
this file forms the coproduct and gives it its universal property, so that the third term is an
object one can name and map into.

Forming it is a question of reachability rather than of existence: the index type is the closed
points of `X`, a `Type u`, while the coefficient universe is `max (u + 1) v`, and at that pair of
universes the colimit is not found by instance search. See
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits`, from which the
colimit used here is taken.

## Main definitions

* `Stacks.EtaleCohomology.closedPointSkyscraper`: the family `x ↦ i_{x,*} ℤ` indexed by the
  closed points of `X`.
* `Stacks.EtaleCohomology.closedPointDivisorSheaf`: its coproduct, the third term of the divisor
  sequence.
* `Stacks.EtaleCohomology.closedPointDivisorSheaf.ι`: the inclusion of the summand at a closed
  point, and the map out of the coproduct determined by a map out of each summand.

## Main results

* `Stacks.EtaleCohomology.hasCoproduct_closedPointSkyscraper`: the coproduct exists.

## Implementation notes

The index is `Topology.closedPoints X`, Mathlib's set of points whose singleton is closed; its
coercion to a type is the subtype `{x // IsClosed {x}}` by
`Topology.mem_closedPoints_iff`. No hypothesis on `X` is needed to form the coproduct, so none is
imposed: the curve hypothesis enters only with the sequence's second map, the order of vanishing,
for which `AlgebraicGeometry.IsCurve.ordHom` supplies the local content.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

variable (X : Scheme.{u})

/-- **The family of skyscraper sheaves `x ↦ i_{x,*} ℤ` over the closed points of a scheme**, whose
coproduct is the third term of the divisor sequence of Stacks 03RM. -/
def closedPointSkyscraper (x : closedPoints X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  integerSkyscraper.{u, v} X x.1

/-- **The coproduct `⨁_x i_{x,*} ℤ` over the closed points of a scheme exists.**

The index type is the closed points of `X`, which is a `Type u` and so is small in the
coefficient universe `max (u + 1) v`; the colimit is then
`AlgebraicGeometry.Scheme.hasColimit_sheaf_smallEtaleTopology`. Instance search does not find it
on its own, which is why this is written down. -/
theorem hasCoproduct_closedPointSkyscraper :
    HasCoproduct (closedPointSkyscraper.{u, v} X) :=
  hasColimit_sheaf_smallEtaleTopology.{u, v} X _

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- **The sheaf `⨁_{x closed} i_{x,*} ℤ` on the small étale site of a scheme**: the coproduct of
`Stacks.EtaleCohomology.closedPointSkyscraper` over the closed points. On a curve this is the
third term of the divisor sequence of Stacks 03RM.

Its sections over an étale `X`-scheme are *not* the direct sum of the sections of the summands:
the coproduct of sheaves is the sheafification of the coproduct of presheaves, which is what
makes the sequence of Stacks 03RM exact on the right. -/
def closedPointDivisorSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  ∐ closedPointSkyscraper.{u, v} X

namespace closedPointDivisorSheaf

/-- **The inclusion of the summand at a closed point** into `⨁_x i_{x,*} ℤ`. -/
def ι (x : closedPoints X) :
    closedPointSkyscraper.{u, v} X x ⟶ closedPointDivisorSheaf.{u, v} X :=
  Sigma.ι (closedPointSkyscraper.{u, v} X) x

end closedPointDivisorSheaf

end Stacks.EtaleCohomology

end
