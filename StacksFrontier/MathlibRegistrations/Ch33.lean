module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Algebra.DualNumber
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of Chapter 33 (Varieties) covered by Mathlib

This file records Stacks Project tags from Chapter 33 (Varieties) whose statements are already
available in Mathlib, by attaching each tag to the Mathlib declarations that state it. When a
tag is covered by several declarations, each registration names the part it covers.

## Tags

* 04PY: the inverse image in `X_K` of a connected component of `X` is a union of connected
  components. Mathlib states this for the inverse image under any continuous map, here the
  projection `X_K → X`, whose inverse image of `T` is the underlying set of `T_K`.
* 0362, 0365, 038K: geometrically connected, geometrically irreducible, and geometrically
  integral. Mathlib states these notions for a morphism `X ⟶ Y`; the tags are the case
  `Y = Spec k`.

Stacks 0385 is not registered here: Mathlib's `Scheme.Hom.connectedComponentsHomeomorph` gives
the bijection on connected components for a geometrically connected morphism that is an open map,
and the tag is proved from it in
`StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ConnectedProductProjection.lean`.

## References

* [Stacks: Varieties](https://stacks.math.columbia.edu/tag/04PY)
-/

@[expose] public section

/- Stacks 09MZ is not registered: Mathlib does not state it (it follows from
`ValuationSubring.mem_or_inv_mem`, but no Mathlib declaration is the statement). -/

add_to_stacks 0B29 "the dual numbers `R[ε]`; as an `R`-module `R × R`, free on `1` and `ε`"
  DualNumber
add_to_stacks 0B29 "the element `ε`" DualNumber.eps
add_to_stacks 0B29 "`ε² = 0`" DualNumber.eps_mul_eps

add_to_stacks 04PY "for the continuous map X_K → X; stated for any continuous map"
  Continuous.preimage_connectedComponent

add_to_stacks 0362 "geometrically connected, for a morphism; the tag is the case of `X ⟶ Spec k`"
  AlgebraicGeometry.GeometricallyConnected

add_to_stacks 0365 "geometrically irreducible, for a morphism; the tag is the case of `X ⟶ Spec k`"
  AlgebraicGeometry.GeometricallyIrreducible

add_to_stacks 038K
  AlgebraicGeometry.GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible
