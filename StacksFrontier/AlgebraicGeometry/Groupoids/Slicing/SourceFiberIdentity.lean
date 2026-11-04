module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceSituation
import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood

/-!
# The identity arrow as a point of a source fibre

Let `G` be a groupoid scheme over a base and let `u` be a point of its object scheme. The
identity arrow `e(u)` is an arrow of `G` whose source is `u`, so it determines a point of the
scheme-theoretic source fibre `F_u = s⁻¹(u)`. This file records that point and its
characterisation, and identifies it with the corresponding field of
`AlgebraicGeometry.SliceIdentityPoints`.

## Main definitions

* `AlgebraicGeometry.sourceFiberIdentity` is the identity arrow at `u`, viewed as a point of the
  source fibre at `u`.

## Main results

* `AlgebraicGeometry.source_identity_apply`: the source of the identity arrow at `u` is `u`.
* `AlgebraicGeometry.fiberι_sourceFiberIdentity` characterises that point: its image under the
  embedding of the source fibre into the arrow scheme is the identity arrow at `u`.
* `AlgebraicGeometry.sourceFiberIdentity_injective_eq` recovers the point from the
  characterisation, the fibre embedding being injective.
* `AlgebraicGeometry.SliceSituation.SliceIdentityPoints.sourceIdentity_eq` identifies the
  `sourceIdentity` field of a `SliceIdentityPoints` with this point.

## Implementation notes

The point is built from `Scheme.Hom.asFiber`, which lands in the fibre over the image of the
given point; transporting along `Stacks.Groupoids.identity_left_comp_source_left` moves it to
the fibre over `u` itself. `fiberι_cast_asFiber` is the transport lemma that makes the
characterisation available after that move.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Transporting a point of a fibre along an equality of base points does not change its image
in the ambient scheme. -/
public alias fiberι_cast_asFiber := Stacks.Flatness.fiberι_cast_asFiber

/-- The source of the identity arrow at `u` is `u`. -/
public theorem source_identity_apply {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) : G.source.left (G.identity.left u) = u := by
  simpa using congrArg (fun f : G.objects.left ⟶ G.objects.left => f u)
    (identity_left_comp_source_left G)

/-- The identity arrow at `u`, viewed as a point of the source fibre `F_u`. -/
public noncomputable def sourceFiberIdentity {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) : G.source.left.fiber u :=
  source_identity_apply G u ▸ G.source.left.asFiber (G.identity.left u)

/-- The identity point of the source fibre sits over the identity arrow. -/
@[simp]
public theorem fiberι_sourceFiberIdentity {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) :
    G.source.left.fiberι u (sourceFiberIdentity G u) = G.identity.left u :=
  fiberι_cast_asFiber _ _ (source_identity_apply G u)

/-- A point of the source fibre lying over the identity arrow is the identity point. -/
public theorem sourceFiberIdentity_injective_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) (x : G.source.left.fiber u)
    (hx : G.source.left.fiberι u x = G.identity.left u) : x = sourceFiberIdentity G u :=
  (G.source.left.fiberι u).isEmbedding.injective
    (hx.trans (fiberι_sourceFiberIdentity G u).symm)

/-- The `sourceIdentity` field of a `SliceIdentityPoints` is the identity point of the source
fibre. -/
public theorem SliceSituation.SliceIdentityPoints.sourceIdentity_eq {D : SliceSituation.{u}}
    (P : SliceSituation.SliceIdentityPoints D) :
    P.sourceIdentity = sourceFiberIdentity D.groupoid D.u :=
  sourceFiberIdentity_injective_eq _ _ _ P.sourceIdentity_fiberι

end AlgebraicGeometry

end
