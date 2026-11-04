module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue fields at points of an affine open

On an affine open `U` of a scheme `X`, the residue field `κ(x)` at a point `x ∈ U` is the residue
field of the prime of `Γ(X, U)` cut out by `x`.

## Main definitions

* `AlgebraicGeometry.residueFieldEquivOfAffineOpen`: the ring isomorphism between `κ(x)` and the
  residue field of the prime of `Γ(X, U)` cut out by `x`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- On an affine open the residue field of a scheme at a point is the residue field of the
prime of the section ring cut out by that point. -/
noncomputable def residueFieldEquivOfAffineOpen
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    X.residueField x ≃+* (hU.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField := by
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization p.primeCompl (X.presheaf.stalk x) :=
    hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime p)).toRingEquiv

end AlgebraicGeometry
