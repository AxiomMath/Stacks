module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksCore.Tactic.StacksAttribute

/-!
# Connected components of a product with a geometrically connected factor

Let `k` be a field and let `X` and `Y` be schemes over `k`. If `X` is geometrically connected
over `k`, then the projection `p : X ×_k Y ⟶ Y` induces a bijection between the connected
components of `X ×_k Y` and those of `Y`.

## Main results

* `AlgebraicGeometry.pullback_snd_connectedComponentsMap_bijective`: the map on connected
  components induced by the projection `X ×_k Y ⟶ Y` is a bijection.

## Implementation notes

A scheme over `k` is its structure morphism `f : X ⟶ Spec k`, the product `X ×_k Y` is the
categorical pullback of `f` along `g : Y ⟶ Spec k`, and the projection of the statement is
`pullback.snd f g`. "Geometrically connected over `k`" is `AlgebraicGeometry.GeometricallyConnected
f`: every base change of `X` along a field-valued point of `Spec k` is a connected space. Since
Mathlib's `ConnectedSpace` includes nonemptiness, this agrees with the source, where a connected
space is nonempty. The induced map on components is pinned rather than merely asserted to exist:
it is `Continuous.connectedComponentsMap` of the projection, sending the component of a point
`z` to the component of `p z`.

The source's proof has three inputs, each supplied by Mathlib or by a sibling statement.

* The scheme-theoretic fibres of `p` are connected, being base changes of the geometrically
  connected `X` by field extensions. Geometric connectedness is stable under base change, so
  `GeometricallyConnected (pullback.snd f g)` is an instance given `GeometricallyConnected f`.
* The scheme-theoretic fibres are homeomorphic to the set-theoretic fibres [stacks, 01K1]. This
  is used inside `AlgebraicGeometry.Scheme.Hom.isConnected_preimage_singleton` through
  `AlgebraicGeometry.Scheme.Hom.range_fiberι`.
* The map `p` is open [stacks, 0383], see `AlgebraicGeometry.universallyOpen_of_field`: the
  structure morphism of a scheme over a field is universally open, so its base change
  `pullback.snd f g` is universally open and `AlgebraicGeometry.Scheme.Hom.isOpenMap` applies.
  This is the only place where `Field k` is used.

The topological conclusion, that an open continuous surjection with connected fibres induces a
bijection on connected components [stacks, 0378], is packaged in Mathlib as
`AlgebraicGeometry.Scheme.Hom.connectedComponentsHomeomorph`.

## References

* [Stacks Project, Tag 0385](https://stacks.math.columbia.edu/tag/0385)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **Stacks 0385.** Let `k` be a field and let `X`, `Y` be schemes over `k`, presented by
their structure maps `f : X ⟶ Spec k` and `g : Y ⟶ Spec k`. If `X` is geometrically connected
over `k`, then the projection `X ×_k Y ⟶ Y` induces a bijection between the connected components
of `X ×_k Y` and the connected components of `Y`. -/
@[stacks 0385]
public theorem pullback_snd_connectedComponentsMap_bijective
    (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [GeometricallyConnected f] :
    Function.Bijective (pullback.snd f g).continuous.connectedComponentsMap := by
  simpa only [Function.Bijective, Function.Injective, Function.Surjective,
    Scheme.Hom.connectedComponentsHomeomorph_apply] using
    ((pullback.snd f g).connectedComponentsHomeomorph (pullback.snd f g).isOpenMap).bijective

end AlgebraicGeometry
