module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Morphisms of big h topoi

A morphism `f : T ⟶ S` of a big h site induces a morphism from the big h topos over `T` to
the big h topos over `S`.  Its inverse image is restriction along postcomposition with `f`
and its direct image is restriction along base change along `f`.

## Main definitions

* `AlgebraicGeometry.bigHMorphismOfTopoi`: the morphism of big h topoi induced by `f`.

## Implementation notes

The big h category over a scheme is a slice of the size-bounded category of schemes of
Stacks 0ETZ, which admits fibre products by Stacks 021U; postcomposition
`CategoryTheory.Over.map` and base change `CategoryTheory.Over.pullback` along `f` are
therefore both defined, and they form an adjoint pair.  Both are continuous for the slice
topologies by Mathlib's generic instances, so the adjunction they form induces an adjunction
between the two restriction functors on sheaves, and the inverse image is left exact because
restriction along a continuous functor preserves all limits.

## References

* [Stacks Project, Tag 0EU6](https://stacks.math.columbia.edu/tag/0EU6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The morphism of big h topoi attached to a morphism `f : T ⟶ S` of a big h site: its
direct image is restriction along base change along `f`, and its inverse image is restriction
along postcomposition with `f`. -/
public noncomputable def bigHMorphismOfTopoi (B : BigHSite.{u}) {T S : B.Schemes}
    (f : T ⟶ S) :
    MorphismOfTopoi
      (Sheaf (BigHOver.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (BigHOver.topology B S.obj S.property) (Type (u + 1))) where
  pushforward := (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
    (B.topology.over S) (B.topology.over T)
  inverseImage := (Over.map f).sheafPushforwardContinuous (Type (u + 1))
    (B.topology.over T) (B.topology.over S)
  adj := (Over.mapPullbackAdj f).sheafPushforwardAdjunction (Type (u + 1))
  preservesFiniteLimits := inferInstance

end AlgebraicGeometry
