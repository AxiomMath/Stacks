module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rational functions and principal divisors on an open subscheme

Let `j : U ⟶ X` be a dominant open immersion of integral schemes — for instance the inclusion of
any nonempty open subscheme of an integral scheme, dominance being supplied by
`Stacks.Chow.isDominant_of_isOpenImmersion`. Then `U` and `X` have the same generic point, so the
same function field, and the local ring of `U` at a point `y` is the local ring of `X` at `j y`.
Divisor theory on `X` is therefore local on `X`: restricting a rational function to `U` changes
neither its order of vanishing at a point nor, consequently, the coefficient of its principal
divisor there.

The restriction of rational functions is recorded in both of the two spellings of the field of
rational functions of an integral scheme: Mathlib's `AlgebraicGeometry.Scheme.functionField`,
where it is `Stacks.Chow.functionFieldEquiv_openImmersion`, and Stacks 01RU's ring `R(X)` of
rational maps to the affine line, where it is
`Stacks.Chow.rationalFunctionsRingEquivOfOpenImmersion`; the two are identified by Stacks 01RV's
isomorphism `Stacks.Chow.rationalFunctionsEquivFunctionField`.

The substance is the invariance of the order of vanishing,
`Stacks.Chow.ord_dominantFunctionFieldMap_of_isOpenImmersion`: an open immersion is an
isomorphism on local rings and, by `AlgebraicGeometry.coheight_eq_of_isOpenImmersion`, does not
change the codimension of a point, and `AlgebraicGeometry.Scheme.ord` depends on nothing else.
The statements below carry that invariance up to the principal divisor `div(f)` of Stacks 0BE3.

## Main definitions

* `Stacks.Chow.rationalFunctionsRingEquivOfOpenImmersion` — the restriction `R(X) ≃+* R(U)` of
  rational functions in the sense of Stacks 01RU, and
  `Stacks.Chow.rationalFunctionsUnitsMulEquivOfOpenImmersion` its restriction to the units.

## Main results

* `Stacks.Chow.ord_functionFieldEquiv_openImmersion` — the order of vanishing of a rational
  function at a point of an open subscheme is its order of vanishing at that point of the
  ambient scheme.
* `Stacks.Chow.principalCycle_functionFieldEquiv_openImmersion_apply`,
  `Stacks.Chow.principalCycle_rationalFunctionsRingEquivOfOpenImmersion_apply` — the coefficient
  of the principal divisor of a rational function at a point of an open subscheme is its
  coefficient at that point of the ambient scheme, for a rational function in the sense of
  Mathlib's function field and in the sense of Stacks 01RU respectively.

## References

* [Stacks Project, Tag 01RU](https://stacks.math.columbia.edu/tag/01RU)
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsIntegral X] [IsIntegral U]
  [IsDominant j]

/-! ### Restriction of rational functions -/

/-- Restricting a rational function to a dominant open subscheme is the extension of function
fields of the open immersion. -/
theorem functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap (f : X.functionField) :
    functionFieldEquiv_openImmersion j f = dominantFunctionFieldMap j f :=
  rfl

/-- The restriction `R(X) ≃+* R(U)` of rational functions in the sense of Stacks 01RU along a
dominant open immersion of integral schemes, read through Stacks 01RV's identification of the
ring of rational functions of an integral scheme with its function field. -/
@[ega "I 7.3.1" "special case"]
def rationalFunctionsRingEquivOfOpenImmersion : rationalFunctions X ≃+* rationalFunctions U :=
  ((rationalFunctionsEquivFunctionField X).1.trans
    (functionFieldEquiv_openImmersion j)).trans (rationalFunctionsEquivFunctionField U).1.symm

/-- `Stacks.Chow.rationalFunctionsRingEquivOfOpenImmersion` is, by construction, the restriction
of the function field read through Stacks 01RV's identification of `R(X)` with the function
field. -/
@[simp]
theorem rationalFunctionsEquivFunctionField_rationalFunctionsRingEquivOfOpenImmersion
    (g : rationalFunctions X) :
    (rationalFunctionsEquivFunctionField U).1 (rationalFunctionsRingEquivOfOpenImmersion j g) =
      functionFieldEquiv_openImmersion j ((rationalFunctionsEquivFunctionField X).1 g) := by
  simp [rationalFunctionsRingEquivOfOpenImmersion]

/-- The restriction of the units of the ring of rational functions — the nonzero rational
functions of Stacks 02RL — to a dominant open subscheme. -/
def rationalFunctionsUnitsMulEquivOfOpenImmersion :
    (rationalFunctions X)ˣ ≃* (rationalFunctions U)ˣ :=
  Units.mapEquiv (rationalFunctionsRingEquivOfOpenImmersion j).toMulEquiv

/-- The underlying rational function of the restriction of a unit of `R(X)` is the restriction
of its underlying rational function. -/
@[simp]
theorem rationalFunctionsUnitsMulEquivOfOpenImmersion_coe (g : (rationalFunctions X)ˣ) :
    ((rationalFunctionsUnitsMulEquivOfOpenImmersion j g : rationalFunctions U)) =
      rationalFunctionsRingEquivOfOpenImmersion j (g : rationalFunctions X) :=
  rfl

/-! ### The order of vanishing -/

variable [IsLocallyNoetherian X] [IsLocallyNoetherian U]

/-- **The order of vanishing is unchanged by restriction to an open subscheme.** The order of
vanishing at `y ∈ U` of the restriction of a rational function on `X` to a dominant open
subscheme `U` is its order of vanishing at `j y`: the two local rings agree, and so do the two
codimensions. -/
theorem ord_functionFieldEquiv_openImmersion (f : X.functionField) (y : U) :
    U.ord (functionFieldEquiv_openImmersion j f) y = X.ord f (j.base y) :=
  ord_dominantFunctionFieldMap_of_isOpenImmersion j f y

/-! ### The principal divisor -/

/-- **The coefficient of a principal divisor is unchanged by restriction to an open subscheme.**
The coefficient at `y ∈ U` of the principal divisor of the restriction of a rational function on
`X` to a dominant open subscheme `U` is the coefficient of `div(f)` at `j y`. -/
theorem principalCycle_functionFieldEquiv_openImmersion_apply (f : X.functionField) (y : U) :
    principalCycle U (functionFieldEquiv_openImmersion j f) y = principalCycle X f (j.base y) := by
  rw [principalCycle_apply, principalCycle_apply, ord_functionFieldEquiv_openImmersion]

/-- **The coefficient of a principal divisor is unchanged by restriction to an open subscheme**,
stated for a rational function in the sense of Stacks 01RU. -/
theorem principalCycle_rationalFunctionsRingEquivOfOpenImmersion_apply (g : rationalFunctions X)
    (y : U) :
    principalCycle U ((rationalFunctionsEquivFunctionField U).1
        (rationalFunctionsRingEquivOfOpenImmersion j g)) y =
      principalCycle X ((rationalFunctionsEquivFunctionField X).1 g) (j.base y) := by
  rw [rationalFunctionsEquivFunctionField_rationalFunctionsRingEquivOfOpenImmersion,
    principalCycle_functionFieldEquiv_openImmersion_apply]

end Stacks.Chow

end
