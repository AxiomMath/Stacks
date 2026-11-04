module

public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedFiniteSeparable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric connectedness over a separable closure

A scheme over a field is geometrically connected if and only if its base change to a
separable algebraic closure of the field is connected.

## Main results

* `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_baseChange` characterizes
  geometric connectedness by a single base change to a separable closure.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`. Its base change
to `ksep` is the categorical pullback of `f` along the morphism of spectra induced by
`algebraMap k ksep`. The separable algebraic closure is given abstractly by an
`IsSepClosure k ksep` instance, so the statement applies to any choice of such a closure.

## References

* [Stacks Project, Tag 0387](https://stacks.math.columbia.edu/tag/0387)
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- Connectedness of a base change descends along a further field extension. -/
@[ega "III 4.3.4" "more general"]
private lemma descend_connectedSpace
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (k' : Type u) [Field k'] [Algebra k k']
    (g : Spec (.of k') ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k' K]
    (y : Spec (.of K) ⟶ Spec (.of k'))
    (h : ConnectedSpace ↥(pullback f (y ≫ g))) :
    ConnectedSpace ↥(pullback f g) := by
  have : ConnectedSpace ↥(pullback y (pullback.fst g f)) :=
    (pullbackRightPullbackFstIso g f y).schemeIsoToHomeo.connectedSpace_iff.mpr
      ((pullbackSymmetry f (y ≫ g)).schemeIsoToHomeo.connectedSpace_iff.mp h)
  exact (pullbackSymmetry g f).schemeIsoToHomeo.connectedSpace_iff.mp
    ((pullback.snd y (pullback.fst g f)).surjective.connectedSpace
      (pullback.snd y (pullback.fst g f)).continuous)

/-- A scheme over a field is geometrically connected if and only if its base change to a
separable algebraic closure is connected. -/
@[stacks 0387]
public theorem geometricallyConnected_iff_connectedSpace_baseChange
    (k : Type u) [Field k] (ksep : Type u) [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔
      ConnectedSpace
        (CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k ksep))) : Scheme.{u}) := by
  refine ⟨fun hf => hf.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _), fun hsep => ?_⟩
  let : IsSepClosed ksep := IsSepClosure.sep_closed (k := k) (K := ksep)
  rw [geometricallyConnected_iff_forall_finite_separable f]
  intro k' _ _ _ _
  let ι : k' →ₐ[k] ksep := IsSepClosed.lift
  let : Algebra k' ksep := ι.toRingHom.toAlgebra
  let y : Spec (.of ksep) ⟶ Spec (.of k') := Spec.map (CommRingCat.ofHom ι.toRingHom)
  have hy : y ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      Spec.map (CommRingCat.ofHom (algebraMap k ksep)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [ι]
  exact descend_connectedSpace f k' _ ksep y (by rwa [hy])

end AlgebraicGeometry
