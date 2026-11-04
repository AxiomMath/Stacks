module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The residue field of `Spec R` at its closed point

For a local ring `R`, the residue field of the scheme `Spec R` at its closed point is the
residue field of the ring `R`.

## Main definitions

* `AlgebraicGeometry.residueFieldAtClosedPointEquiv`: the ring isomorphism between the two.

## Implementation notes

The isomorphism is `IsLocalRing.ResidueField.mapEquiv` applied to
`AlgebraicGeometry.stalkClosedPointIso`, the identification of the stalk of `Spec R` at the
closed point with `R`.  Transporting the local-ring structure along
`AlgebraicGeometry.Spec.stalkIso` is what lets the residue field of that stalk be formed.

This module exists to be the single home of a fact that was proved privately in two mutually
incomparable modules.  Neither of those owns the vocabulary — the statement is about `Spec` of a
local ring and its residue field, not about either of their subjects — so the fact lives here, in
a module small enough that importing it costs nothing.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- **The residue field of `Spec R` at its closed point is the residue field of `R`.**  For a
local ring `R`, the closed point of `Spec R` is `IsLocalRing.closedPoint R`, and the residue
field of the scheme there is canonically the residue field of the ring. -/
@[ega "I 10.1.6" "special case"]
public def residueFieldAtClosedPointEquiv
    {R : CommRingCat.{u}} [IsLocalRing R] :
    (Spec R).residueField (IsLocalRing.closedPoint R : Spec R) ≃+*
      IsLocalRing.ResidueField R := by
  let cp : Spec R := IsLocalRing.closedPoint R
  letI : IsLocalRing ((Spec R).presheaf.stalk cp) :=
    (Spec.stalkIso R cp).commRingCatIsoToRingEquiv.symm.isLocalRing
  exact IsLocalRing.ResidueField.mapEquiv
    (stalkClosedPointIso R).commRingCatIsoToRingEquiv

end AlgebraicGeometry

end
