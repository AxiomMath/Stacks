module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedFiniteSeparable
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometrically connected fibres and étale neighbourhoods

The fibre of a morphism of schemes at a point is geometrically connected exactly when its
pullback to every étale neighbourhood of that point has connected fibre at the distinguished
point. This is the criterion behind the Stein factorization: geometric connectedness of a
fibre, a statement about an algebraically closed extension of the residue field, is detected by
the finitely many connected components appearing over étale neighbourhoods.

## Main results

* `AlgebraicGeometry.geometricallyConnected_fiber_iff_forall_etaleNeighborhood` characterizes a
  geometrically connected fibre using étale neighbourhoods.

## Implementation notes

An étale neighbourhood is represented by `AlgebraicGeometry.EtaleNeighborhood`. The base change
of `f : X ⟶ S` to such a neighbourhood `U` is the chosen pullback, with structure morphism
`pullback.snd f U.toBase`; its fibre at `U.point` is required to be connected.

The forward implication is the definition of geometric connectedness applied to the pullback
square. The converse uses that geometric connectedness is detected by finite separable
extensions (Tag 0389) together with the realization of every such extension as the residue
field of an étale neighbourhood (Tag 02LF).

## References

* [Stacks Project, Tag 03GZ](https://stacks.math.columbia.edu/tag/03GZ)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Connectedness of the fibre of a base change at a point is the connectedness of the
pullback of the fibre over the residue field along the residue field extension. -/
private lemma connectedSpace_fiber_iff_baseChange {P X S U : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ U} {f : X ⟶ S} {g : U ⟶ S}
    (h : IsPullback a b f g) (y : U) : ConnectedSpace (b.fiber y) ↔
    ConnectedSpace (pullback (f.fiberToSpecResidueField (g y))
      (Spec.map (g.residueFieldMap y)) : Scheme.{u}) :=
  ((isPullback_fiberToSpecResidueField_of_isPullback h y).flip.isoIsPullback
    _ _ (IsPullback.of_hasPullback _ _).flip).hom.homeomorph.connectedSpace_iff

/-- Connectedness of a base change along a field extension only depends on the extension up to
isomorphism of extensions. -/
private lemma connectedSpace_pullback_of_algEquiv {k k' K : Type u}
    [Field k] [Field k'] [Field K] [Algebra k k'] [Algebra k K]
    (e : k' ≃ₐ[k] K) {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (h : ConnectedSpace (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u})) :
    ConnectedSpace (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) := by
  let i : Spec (.of k') ⟶ Spec (.of K) := Spec.map e.symm.toRingEquiv.toCommRingCatIso.hom
  have hi : Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      i ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    dsimp [i]
    rw [← Spec.map_comp]
    congr 1
    ext x
    change (algebraMap k k') x = e.symm ((algebraMap k K) x)
    exact (e.symm.commutes x).symm
  have : IsIso i := by
    dsimp [i]
    infer_instance
  exact (asIso (pullback.map _ _ _ _ (𝟙 _) i (𝟙 _) (by simp)
    (by simpa using hi))).hom.homeomorph.connectedSpace_iff.mp h

/-- **Stacks Project, Tag 03GZ.** The fibre of a morphism at a point is geometrically connected
if and only if the fibre at the distinguished point after pullback to every étale neighborhood
is connected. -/
@[stacks 03GZ]
theorem geometricallyConnected_fiber_iff_forall_etaleNeighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    GeometricallyConnected (f.fiberToSpecResidueField s) ↔
      ∀ U : EtaleNeighborhood S s,
        ConnectedSpace ((pullback.snd f U.toBase).fiber U.point) := by
  refine ⟨fun hf U => (connectedSpace_fiber_iff_baseChange
    (IsPullback.of_hasPullback f U.toBase) U.point).2 <|
      (U.map_point.symm ▸ hf).geometrically_connectedSpace _ _ _ (.of_hasPullback _ _),
    fun h => ?_⟩
  rw [geometricallyConnected_iff_forall_finite_separable]
  intro k _ _ _ _
  have : Module.Finite (S.residueField s) k := inferInstance
  obtain ⟨U, ⟨e⟩⟩ := exists_etaleNeighborhood_residueField_algEquiv S s k
  have hU := (connectedSpace_fiber_iff_baseChange
    (IsPullback.of_hasPullback f U.toBase) U.point).1 (h U)
  let : Algebra (S.residueField s) (U.scheme.residueField U.point) :=
    U.residueFieldMap.hom.toAlgebra
  refine connectedSpace_pullback_of_algEquiv e (f.fiberToSpecResidueField s) ?_
  cases U with
  | mk T y g heq =>
    cases heq
    have hm : Spec.map (g.residueFieldMap y) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField (g y)) (T.residueField y))) := rfl
    exact (pullback.congrHom rfl hm).hom.homeomorph.connectedSpace_iff.mp hU

end AlgebraicGeometry
