module

public import Mathlib.Topology.LocallyFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique

/-!
# Inverse images of closed sets and of locally finite collections of points

A morphism of algebraic spaces over a scheme `S` is continuous for the canonical topologies on
the spaces of points. Consequently it pulls closed subsets back to closed subsets and locally
finite collections of subsets back to locally finite collections. These are the two
set-theoretic facts needed to pull a cycle back along a flat morphism: they guarantee that the
support of the pullback is again a locally finite collection of closed subsets.

## Main results

* `AlgebraicGeometry.Space.isClosed_preimage_pointsMap`: **Stacks 0EP6**, closedness of the
  inverse image of a closed subset.
* `AlgebraicGeometry.Space.locallyFinite_preimage_pointsMap`: **Stacks 0EP6**, local finiteness
  of the inverse image of a locally finite collection.

## Implementation notes

Both statements hold for arbitrary algebraic spaces over `S`; neither the good-space hypotheses
nor a fixed base space is needed, so they are stated for a bare morphism `f : X ⟶ Y` of
algebraic spaces. The topologies are `AlgebraicGeometry.Space.pointTopology`, introduced by
`letI` in the statements so that the conclusions can mention `IsOpen` and `LocallyFinite`
without a topology argument; continuity is
`AlgebraicGeometry.Space.continuous_pointsMap`, which needs no algebraic-space hypothesis.

The algebraic-space hypotheses on source and target are therefore unused; they are retained,
with underscores, so that the statements are the ones of Stacks 0EP6.

A locally finite collection of subsets of a topological space, Stacks 0BDS, is Mathlib's
`LocallyFinite`.

## References

* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0BDS](https://stacks.math.columbia.edu/tag/0BDS)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

/-- **Stacks 0EP6, closedness.** The inverse image of a closed subset of the points of `Y`
under a morphism `f : X ⟶ Y` of algebraic spaces over `S` is closed in the points of `X`. -/
@[stacks 0EP6 "closedness"]
theorem isClosed_preimage_pointsMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X)
    (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    letI : TopologicalSpace (points B S hS X) := pointTopology B S hS X
    letI : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
    ∀ {T : Set (points B S hS Y)}, IsClosed T →
      IsClosed ((pointsMap B S hS X f) ⁻¹' T) := by
  let _ := pointTopology B S hS X
  let _ := pointTopology B S hS Y
  exact fun _ hT ↦ hT.preimage (continuous_pointsMap B S hS f)

/-- **Stacks 0EP6, local finiteness.** The inverse images of a locally finite collection of
subsets of the points of `Y` under a morphism `f : X ⟶ Y` of algebraic spaces over `S` form a
locally finite collection of subsets of the points of `X`. -/
@[stacks 0EP6 "local finiteness"]
theorem locallyFinite_preimage_pointsMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X)
    (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type v} (T : I → Set (points B S hS Y)) :
    letI : TopologicalSpace (points B S hS X) := pointTopology B S hS X
    letI : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
    LocallyFinite T →
      LocallyFinite (fun i ↦ (pointsMap B S hS X f) ⁻¹' T i) := by
  let _ := pointTopology B S hS X
  let _ := pointTopology B S hS Y
  exact fun hT ↦ hT.preimage_continuous (continuous_pointsMap B S hS f)

end AlgebraicGeometry.Space

end
