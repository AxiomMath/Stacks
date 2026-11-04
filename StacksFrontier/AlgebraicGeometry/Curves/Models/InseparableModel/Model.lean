module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality

/-!
# A regular model with an inseparable component: the situation

The data of `Stacks.Models.InseparableModel` assemble into a regular proper model of the
projective line over `K = Frac 𝔽₂(t)⟦π⟧`.

## Main definitions

* `Stacks.Models.InseparableModel.situation` — the regular proper model.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace Stacks.Models.InseparableModel

/-- **The regular proper model**: `X ⟶ Spec R` with generic fibre `X_K`. -/
def situation : RegularProperModelSituation.{0} where
  R := R
  K := K
  k := k
  residueEquiv := residueEquiv
  C := genericFibre
  C_to_K := genericFibreToK
  X := XR
  X_to_R := X_to_R
  regular := isRegular_XR
  genericFiberIso := Iso.refl _
  genericFiberIso_over_K := by simp
  π := π
  uniformizer := irreducible_π
  curveProjective := isHProjective_genericFibre

end Stacks.Models.InseparableModel
