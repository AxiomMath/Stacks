module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two helpers for the specialization map

Connectedness of a proper family over a local ring, and the reconciliation of the two
conventional residue fields of a local ring. Both are used by several of the modules building
the specialization map of [Stacks, Tag 0BUP] and its functoriality.

## Main results

* `AlgebraicGeometry.connectedSpace_of_universallyClosed_geometricallyConnected` and
  `AlgebraicGeometry.connectedSpace_pullback_spec_of_isProper`: a universally closed morphism
  with geometrically connected fibres over a connected base has connected source, and the base
  change of a proper such morphism along a morphism out of the spectrum of a local ring is
  connected.
* `AlgebraicGeometry.residueFieldEquivMaximalIdealResidueField`: the quotient of a local ring by
  its maximal ideal and the residue field of the localization at it agree, and
  `AlgebraicGeometry.algebraMap_residueField_residue` identifies the comparison map on residues.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A universally closed morphism with geometrically connected fibres and connected target has
connected source: it is a quotient map, and the preimage of every point is connected. -/
@[ega "IV 4.4.2" "special case"]
theorem connectedSpace_of_universallyClosed_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] [GeometricallyConnected f]
    [ConnectedSpace S] : ConnectedSpace X := by
  have hq : Topology.IsCoinducing f :=
    (f.isClosedMap.isQuotientMap f.continuous f.surjective).isCoinducing
  have hc : _root_.IsConnected (Set.univ : Set X) := by
    simpa using Topology.IsCoinducing.isConnected_preimage_of_isClosed
      f.isConnected_preimage_singleton hq isClosed_univ isConnected_univ
  exact connectedSpace_iff_univ.mpr (by simpa using hc)

/-- The base change of a proper morphism with geometrically connected fibres along a morphism out
of the spectrum of a local ring is connected. -/
theorem connectedSpace_pullback_spec_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] (R : Type u) [CommRing R] [IsLocalRing R]
    (r : Spec (.of R) ⟶ S) : ConnectedSpace (pullback f r : Scheme.{u}) :=
  have := connectedSpace_spec_of_isLocalRing R
  connectedSpace_of_universallyClosed_geometricallyConnected (pullback.snd f r)

/-- The canonical map between the two conventional residue fields of a local ring carries the
residue of a ring element to its image. -/
theorem algebraMap_residueField_residue (R : Type u) [CommRing R] [IsLocalRing R] (x : R) :
    algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R x)
      = algebraMap R (maximalIdeal R).ResidueField x :=
  (IsScalarTower.algebraMap_apply R (ResidueField R) (maximalIdeal R).ResidueField x).symm

/-- The two conventional residue fields of a local ring agree: the quotient by the maximal ideal
and the residue field of the localization at it. -/
noncomputable def residueFieldEquivMaximalIdealResidueField (R : Type u) [CommRing R]
    [IsLocalRing R] :
    ResidueField R ≃+* (maximalIdeal R).ResidueField :=
  RingEquiv.ofBijective (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    ⟨RingHom.injective _, fun y ↦ by
      obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal R) y
      exact ⟨residue R x, algebraMap_residueField_residue R x⟩⟩

end AlgebraicGeometry

end
