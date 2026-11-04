module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic

/-!
# The two models of `I ^ n • F` agree

`Stacks.Algebraization.idealPowerMultiple` and
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` are both the least subsheaf of `F`
containing `I(U) ^ n • Γ(F, U)` on every affine open `U`, so they are equal.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerComparison.algebraization_idealPowerMultiple_eq`: the two
  subsheaves agree.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerComparison

variable {X : Scheme.{u}}

/-- **The two models of `I ^ n • F` agree**: `Stacks.Algebraization.idealPowerMultiple` and
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` are both the least subsheaf of `F`
containing `I(U) ^ n • Γ(F, U)` on every affine open `U`. -/
theorem algebraization_idealPowerMultiple_eq (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    Stacks.Algebraization.idealPowerMultiple I n F = idealPowerMultiple I n F :=
  le_antisymm
    ((Stacks.Algebraization.idealPowerMultiple_le_iff I n F _).2
      (le_idealPowerMultiple_obj I n F))
    ((idealPowerMultiple_le_iff I n F _).2
      ((Stacks.Algebraization.idealPowerMultiple_le_iff I n F _).1 le_rfl))

end Stacks.AlgebraicGeometry.IdealPowerComparison

end
