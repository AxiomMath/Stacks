module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue fields of points of the spectrum of a field

Every point `x` of `Spec k`, for `k` a field, has residue field canonically isomorphic to `k`,
by way of `Ideal.algEquivResidueFieldOfField` and `AlgebraicGeometry.Scheme.Spec.residueFieldIso`.
This file records that this identification is compatible with transporting residue fields along an
equality of points.

## Main results

* `AlgebraicGeometry.spec_residueFieldEquiv_congr`: the canonical isomorphism `k ≃+* κ(x)`
  commutes with `AlgebraicGeometry.Scheme.residueFieldCongr`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Transporting the residue field of a point of the spectrum of a field along an equality of
points is compatible with the canonical identification with that field. -/
public lemma spec_residueFieldEquiv_congr (k : Type u) [Field k]
    (x y : Spec (.of k)) [x.asIdeal.IsPrime] [y.asIdeal.IsPrime] (h : x = y) (z : k) :
    (Scheme.residueFieldCongr h).hom
        ((Scheme.Spec.residueFieldIso (.of k) x).symm.commRingCatIsoToRingEquiv
          (x.asIdeal.algEquivResidueFieldOfField.toRingEquiv z)) =
      (Scheme.Spec.residueFieldIso (.of k) y).symm.commRingCatIsoToRingEquiv
        (y.asIdeal.algEquivResidueFieldOfField.toRingEquiv z) := by
  cases h; rfl

end AlgebraicGeometry

end
