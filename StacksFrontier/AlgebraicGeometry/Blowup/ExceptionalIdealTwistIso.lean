module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The ideal sheaf of a divisor as a Rees-algebra piece

The sheaf `Stacks.Divisors.negativeTwist' D`, the ideal sheaf `ℐ_D ⊆ 𝒪_X` of a closed subscheme
`D`, and the degree-one piece `Stacks.Blowup.idealPowerKernel D 1` of the Rees algebra of `D`
are literally the same kernel: both are the kernel of `𝒪_X ⟶ (ι)_* 𝒪_{V(D)}`, one spelled at
the level of ringed spaces and the other at the level of schemes.

## Main results

* `Stacks.Blowup.negativeTwist'_eq_idealPowerKernel`: the identification.

## References

* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

/-- The ideal sheaf `𝒪_X(-D)` of a closed subscheme `D`, in the spelling
`Stacks.Divisors.negativeTwist'`, is the degree-one piece of the Rees algebra of `D`: both are
the kernel of `𝒪_X ⟶ (ι_D)_* 𝒪_D`, one spelled at ringed spaces and the other at schemes. -/
theorem negativeTwist'_eq_idealPowerKernel {X : Scheme.{u}} (D : X.IdealSheafData) :
    Stacks.Divisors.negativeTwist' D = idealPowerKernel D 1 :=
  (congrArg (fun J : X.IdealSheafData =>
      kernel (SheafOfModules.unitToPushforwardObjUnit (J.subschemeι.toRingCatSheafHom)))
    (pow_one D)).symm

end Stacks.Blowup

end
