module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometric connectedness after a field extension

Geometric connectedness of a scheme over a field may be checked after extending the
base field.

## Main results

* `AlgebraicGeometry.geometricallyConnected_iff_baseChange_fieldExtension` states that a scheme
  over a field is geometrically connected if and only if its base change along any field
  extension is geometrically connected.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`. Its base change
to `k'` is represented by the pullback projection to `Spec k'`.

## References

* [Stacks Project, Tag 054N](https://stacks.math.columbia.edu/tag/054N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 054N.** A scheme over a field is geometrically connected if and only if
its base change along a field extension is geometrically connected. -/
@[stacks 054N]
public theorem geometricallyConnected_iff_baseChange_fieldExtension
    {X : Scheme.{u}} (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔
      GeometricallyConnected
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  let g : Spec (.of k') ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k'))
  change GeometricallyConnected f ↔ GeometricallyConnected (pullback.snd f g)
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ⟨?_⟩⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  obtain ⟨M, _, _, _, _, _, _⟩ := exists_common_extension k k' K
  let y : Spec (.of M) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' M))
  let z : Spec (.of M) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K M))
  let q : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have heq : z ≫ q = y ≫ g := by
    dsimp [y, z, g, q]
    simp only [← Spec.map_comp]
    congr 1
    ext x
    exact (IsScalarTower.algebraMap_apply k K M x).symm.trans
      (IsScalarTower.algebraMap_apply k k' M x)
  have hc : ConnectedSpace ↥(pullback f (z ≫ q)) := by
    rw [heq]
    exact (pullbackLeftPullbackSndIso f g y).schemeIsoToHomeo.connectedSpace_iff.mp
      (h.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _))
  have : ConnectedSpace ↥(pullback z (pullback.fst q f)) :=
    (pullbackRightPullbackFstIso q f z).schemeIsoToHomeo.connectedSpace_iff.mpr
      ((pullbackSymmetry f (z ≫ q)).schemeIsoToHomeo.connectedSpace_iff.mp hc)
  exact (pullbackSymmetry q f).schemeIsoToHomeo.connectedSpace_iff.mp
    ((pullback.snd z (pullback.fst q f)).surjective.connectedSpace
      (pullback.snd z (pullback.fst q f)).continuous)

end AlgebraicGeometry
