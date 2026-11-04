module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol

/-!
# The residue field at a point is the function field of its integral component

Let `ξ` be a point of a scheme `X` and let `Z_ξ = Stacks.Chow.integralComponentAt ξ` be the
integral closed subscheme of `X` attached to it, that is, the closure of `ξ` with its reduced
structure. Its generic point is `ξ`, so its field of rational functions is the residue field
`κ(ξ)` of the local ring `𝒪_{X, ξ}`. This is the identification the key formula Stacks 0AYC uses
when it reads the tame symbol `∂_{B_i}(f_i, g_i) ∈ κ(ξ_i)^*` as a rational function on `Z_i`, and
when it reads the image `u|_{Z_i}` of a unit of `B_i` in the residue field as a rational function
on `Z_i`.

At the `Stacks.Chow.rationalFunctions` spelling the identification is
`Stacks.Chow.rationalFunctionsIntegralComponentEquiv`, with unit version
`Stacks.Chow.rationalFunctionsUnitsIntegralComponentEquiv`. This file re-spells it onto Mathlib's
`AlgebraicGeometry.Scheme.functionField` — the stalk of `Z_ξ` at its generic point. That is the
field in which the order of vanishing `Stacks.Divisors.orderOfVanishing` of a meromorphic section
takes its coordinates, so it is the spelling a divisor *on* `Z_ξ` is computed in.

Both equivalences are isomorphisms of fields, so a unit of either side transports to a unit of
the other; `Stacks.Chow.functionFieldUnitsIntegralComponentEquiv` performs that transport.

## Main definitions

* `Stacks.Chow.functionFieldIntegralComponentEquiv` — `R(Z_ξ) ≃+* κ(ξ)`, with `R(Z_ξ)` spelled as
  `AlgebraicGeometry.Scheme.functionField`.
* `Stacks.Chow.functionFieldUnitsIntegralComponentEquiv` — the same on units.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **The function field of `Z_ξ` is the residue field of `𝒪_{X, ξ}`.** The integral closed
subscheme `Z_ξ = Stacks.Chow.integralComponentAt ξ` has generic point `ξ`, so its function field
— the stalk of `Z_ξ` at that generic point — is `κ(ξ)`.

This is `Stacks.Chow.rationalFunctionsIntegralComponentEquiv` composed with Stacks 01RV, the
identification `Stacks.Chow.rationalFunctionsEquivFunctionField` of the rational functions of an
integral scheme with its function field. -/
def functionFieldIntegralComponentEquiv (x : X) :
    letI := isIntegral_integralComponentAt x
    (integralComponentAt x).subscheme.functionField ≃+*
      IsLocalRing.ResidueField (X.presheaf.stalk x) :=
  letI := isIntegral_integralComponentAt x
  ((rationalFunctionsEquivFunctionField (integralComponentAt x).subscheme).1.symm.trans
    (rationalFunctionsIntegralComponentEquiv x))

/-- **A unit of the function field of `Z_ξ` is a unit of `κ(ξ)`**, and conversely: the
identification of the two fields is an isomorphism of rings, so it carries units to units.

This is the shape in which the key formula Stacks 0AYC uses the identification. Its tame symbols
take values in `κ(ξ_i)^*` and its restricted divisors are divisors of meromorphic sections on
`Z_i`, whose coordinates are units of `R(Z_i)`. -/
def functionFieldUnitsIntegralComponentEquiv (x : X) :
    letI := isIntegral_integralComponentAt x
    ((integralComponentAt x).subscheme.functionField)ˣ ≃*
      (IsLocalRing.ResidueField (X.presheaf.stalk x))ˣ :=
  letI := isIntegral_integralComponentAt x
  Units.mapEquiv (functionFieldIntegralComponentEquiv x).toMulEquiv

/-- The transport of a unit of `R(Z_ξ)` to `κ(ξ)` agrees with the underlying ring isomorphism. -/
@[simp]
theorem functionFieldUnitsIntegralComponentEquiv_coe (x : X)
    (u : letI := isIntegral_integralComponentAt x
      ((integralComponentAt x).subscheme.functionField)ˣ) :
    letI := isIntegral_integralComponentAt x
    ((functionFieldUnitsIntegralComponentEquiv x u : _) :
        IsLocalRing.ResidueField (X.presheaf.stalk x)) =
      functionFieldIntegralComponentEquiv x (u : _) :=
  rfl

end Stacks.Chow

end
