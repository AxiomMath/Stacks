module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition and base change between slices of a big site

Let `B` be a big site whose underlying category is cut out of schemes by a cardinal bound, and
let `f : T ⟶ S` be a morphism of it. Composition with `f` carries the slice over `T` to the
slice over `S`, and has a right adjoint given by base change along `f`. For the localized
topologies, composition is cocontinuous and base change is continuous, so the pair is a
morphism of sites.

Both halves are Mathlib's general results about slice categories and localized topologies; what
has to be supplied here is that the cutoff category actually has the fibre products those
results need.

## Main results

* `AlgebraicGeometry.schemeCutoff_hasPullbacks` — the cutoff category of a big smooth site has
  fibre products.
* `CategoryTheory.Over.mapPullbackAdj` — composition is left adjoint to base change.
* `CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver` — base change is
  continuous for the localized topologies.
* `CategoryTheory.GrothendieckTopology.instIsCocontinuousOverMapOver` — composition is
  cocontinuous for the localized topologies.

## Implementation notes

A size cutoff is an `ObjectProperty` on schemes, and two closure properties are exactly what
make its full subcategory inherit fibre products: invariance under isomorphism lets the
property be transported along the canonical isomorphism identifying a limit of a cospan with
the chosen fibre product, and closure under cospans is then the statement that the size of a
fibre product stays below the cutoff. Both are supplied by the imported instances
`AlgebraicGeometry.schemeSizeBelow_isClosedUnderIsomorphisms` and
`AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan`, so the cutoff
category has pullbacks by typeclass inference and Mathlib's slice results apply verbatim.

The source's functor `u` is `CategoryTheory.Over.map f` and its functor `v` is
`CategoryTheory.Over.pullback f`, the latter sending `U ⟶ S` to the chosen fibre product
`U ×_S T ⟶ T`.

## References

* [Stacks Project, Tag 04HC](https://stacks.math.columbia.edu/tag/04HC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The bounded category underlying a big smooth site has pullbacks. -/
public instance schemeCutoff_hasPullbacks (B : BigSmoothSite.{u}) :
    HasPullbacks B.category :=
  inferInstance

add_to_stacks 04HC "continuous_right_adjoint" CategoryTheory.Over.mapPullbackAdj
add_to_stacks 04HC "continuous_right_adjoint"
  CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver

add_to_stacks 04HC "cocontinuity"
  CategoryTheory.GrothendieckTopology.instIsCocontinuousOverMapOver

end AlgebraicGeometry
