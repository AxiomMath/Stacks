module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapRationalEquivalenceReduction
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge

/-!
# The first Chern class cap product on Chow groups

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. Stacks 02TI asserts that
for `X` locally of finite type over `S` and `ℒ` an invertible `𝒪_X`-module the cap product
`α ↦ c₁(ℒ) ∩ α` of Stacks 02SO kills every `(k+1)`-cycle rationally equivalent to zero, so that
it descends to `c₁(ℒ) ∩ - : A_{k+1}(X) ⟶ A_k(X)`.

`Stacks.Chow.firstChernCapFactorsEverywhere_iff_killsPrincipalDivisor` reduces that assertion to
its integral case, the vanishing of `c₁(ℒ) ∩ div_Z(f)` for `Z` integral and locally Noetherian of
delta-dimension `k + 2` and `f` a nonzero rational function on `Z`. The integral case is
`Stacks.Chow.KeyFormulaSituation.firstChernClassCapOfInvertible_weilDivisorCycleN`, proved from
the key formula of Stacks 0AYC, and the situation of Stacks 0AYB it is stated against exists for
any two nonzero meromorphic sections, by `Stacks.Chow.keyFormulaSituationOf`. Both halves are
therefore available with no hypothesis, and this file joins them.

What the junction needs is the comparison of two descriptions of one cycle. The reduction
quantifies over cycles whose underlying cycle is the principal divisor
`div(f) = ∑_Z ord_Z(f) [Z]`, while the integral case is stated for the divisor cycle
`div_{𝒪_Z}(f)` of the meromorphic section of the structure sheaf with generic value `f`. The two
agree: the germ of `1` is a basis of every stalk of `𝒪_Z`, so `f` is a coordinate of itself at
every point, and the order of vanishing of the section along a prime divisor is therefore
`ord_ξ(f)` by the characterization of Stacks 02SF.

## Main definitions

* `Stacks.Chow.firstChernClassCapChow` — intersection with the first Chern class of an invertible
  module, as an operation `A_{k+1}(X) ⟶ A_k(X)`.

## Main results

* `Stacks.Chow.orderOfVanishing_unitModule_eq_ord` — a meromorphic section of `𝒪_X` with generic
  value `f` has order of vanishing `ord_ξ(f)` along every prime divisor.
* `Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_eq_principalCycle` —
  `div_{𝒪_X}(f) = div(f)`.
* `Stacks.Chow.firstChernCapKillsPrincipalDivisor` — the integral case of Stacks 02TI, for every
  integral scheme of delta-dimension `k + 2`, every invertible module on it and every nonzero
  rational function.
* `Stacks.Chow.firstChernCapFactorsEverywhere` — **Stacks 02TI**: the cap product with the first
  Chern class of an invertible module kills every cycle rationally equivalent to zero, for every
  scheme locally of finite type over the base.

## References

* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

open Stacks.Ample (unitModule unitStalkEquiv)

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The divisor of a rational function as the divisor of a section of the structure sheaf -/

section Principal

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **The order of vanishing of a rational function, Stacks 02SF for `𝒪_X`.** The meromorphic
section of `𝒪_X` whose generic value corresponds to `f` has order of vanishing `ord_ξ(f)` along
every prime divisor `Z` with generic point `ξ`: the germ of `1` is a basis of the stalk at `ξ`, so
`f` is a coordinate of the section there. -/
theorem orderOfVanishing_unitModule_eq_ord (f : X.functionField)
    (Z : Stacks.Divisors.PrimeDivisor X) :
    orderOfVanishing (unitModule X) ((unitStalkEquiv X (genericPoint X)).symm f) Z =
      X.ord f Z.genericPoint :=
  have := isInvertible_presheaf (unitModule X)
  orderOfVanishing_eq (isTrivializedNear_of_isInvertible (unitModule X) Z.genericPoint)
    (isCoordinateAt_unitModule X Z.genericPoint f)

variable {L : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **`div_{𝒪_X}(f) = div(f)`.** The divisor cycle of the section `t` of a situation whose second
module is the structure sheaf is the principal divisor of the rational function `t` corresponds
to: along a prime divisor the two coefficients are the order of vanishing of `t` and the order of
`f`, and both cycles vanish outside codimension one. -/
theorem KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_eq_principalCycle
    (ℱ : KeyFormulaSituation L (unitModule X)) (f : X.functionField)
    (hf : ℱ.sectionN = (unitStalkEquiv X (genericPoint X)).symm f) :
    weilDivisorAlgebraicCycle ℱ.weilDivisorN = principalCycle X f := by
  have := isInvertible_presheaf (unitModule X)
  have hdiv : ℱ.weilDivisorN =
      weilDivisorOfMeromorphicSection (isTrivializedNear_of_isInvertible (unitModule X))
        ((unitStalkEquiv X (genericPoint X)).symm f) := by
    rw [← hf]
  refine Function.locallyFinsuppWithin.ext fun x => ?_
  rw [weilDivisorAlgebraicCycle_apply, hdiv, principalCycle_apply]
  by_cases hx : coheight x = 1
  · have hgen : (Stacks.Divisors.PrimeDivisor.ofCoheightOne x hx).genericPoint = x :=
      Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne x hx
    rw [← hgen, weilDivisorCoeff_genericPoint,
      Stacks.Divisors.weilDivisorOfMeromorphicSection_apply,
      orderOfVanishing_unitModule_eq_ord]
  · rw [weilDivisorCoeff_eq_zero_of_coheight_ne_one _ hx,
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

end Principal

/-! ### Stacks 02TI -/

variable (C : ChowSituation.{u}) (k : ℤ)

/-- **The integral case of Stacks 02TI, with no hypothesis.** On an integral, locally Noetherian
scheme `Z` of delta-dimension `k + 2` locally of finite type over the base, intersecting the
principal divisor of a nonzero rational function with the first Chern class of an invertible
module gives zero in `A_k(Z)`.

The cycle is any `(k+1)`-cycle presenting `div(f)`, so it is the divisor cycle of the meromorphic
section of `𝒪_Z` with generic value `f`, and the vanishing is
`Stacks.Chow.firstChernClassCapOfInvertible_weilDivisorCycle_eq_zero` for the situation of
Stacks 0AYB built from that section and a nonzero meromorphic section of the module. -/
theorem firstChernCapKillsPrincipalDivisor : FirstChernCapKillsPrincipalDivisor C k := by
  intro Z q _ _ _ hq M _ f hf β hβ
  have hinv := isInvertible_presheaf M
  obtain ⟨s, hs⟩ := exists_ne_zero_genericStalk_of_isInvertible M
  have hf' : (unitStalkEquiv Z (genericPoint Z)).symm f ≠ 0 := fun h0 => hf (by
    have h1 := congrArg (unitStalkEquiv Z (genericPoint Z)) h0
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h1)
  have hn : schemeDeltaDimension C q = ((k + 2 : ℤ) : EInt) := by
    rw [hq, show (k + 1 + 1 : ℤ) = k + 2 from by ring]
  have hβeq : β = (keyFormulaSituationOf M (unitModule Z) s
      ((unitStalkEquiv Z (genericPoint Z)).symm f) hs hf').weilDivisorCycleN C q hn :=
    Subtype.ext (hβ.trans
      (KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_eq_principalCycle _ f rfl).symm)
  rw [hβeq]
  exact firstChernClassCapOfInvertible_weilDivisorCycle_eq_zero C q hn hs hf'

/-- **Stacks 02TI, with no hypothesis.** Intersecting with the first Chern class of an invertible
module kills every `(k+1)`-cycle rationally equivalent to zero, whatever the scheme locally of
finite type over the base and whatever the module.

This is the reduction of `Stacks.Chow.firstChernCapFactorsEverywhere_iff_killsPrincipalDivisor`
supplied with its integral case. -/
@[stacks 02TI "the factoring itself, with no hypothesis: capping with the first Chern class of \
an invertible module kills every cycle rationally equivalent to zero, for every scheme locally \
of finite type over the base and every module"]
theorem firstChernCapFactorsEverywhere : FirstChernCapFactorsEverywhere C k :=
  (firstChernCapFactorsEverywhere_iff_killsPrincipalDivisor C k).2
    (firstChernCapKillsPrincipalDivisor C k)

/-! ### The descended cap product -/

variable {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Stacks 02TI for one scheme and one invertible module.** The cap product with the first Chern
class of `L` factors through rational equivalence in degree `k`. -/
theorem firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule :
    FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k L) :=
  firstChernCapFactorsEverywhere C k X p L

/-- **Stacks 02TI.** Intersection with the first Chern class of an invertible module, as an
operation `c₁(L) ∩ - : A_{k+1}(X) ⟶ A_k(X)` on Chow groups. -/
@[stacks 02TI "the descended operation c_1(L) cap - : A_{k+1}(X) ⟶ A_k(X), agreeing with the \
cap product of 02SO on cycle representatives (firstChernClassCapChow_mk)"]
def firstChernClassCapChow : chowGroup C p (k + 1) →+ chowGroup C p k :=
  firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k L)
    (firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k p L)

/-- The descended operation agrees with the cap product on cycle representatives. -/
@[simp]
theorem firstChernClassCapChow_mk (α : CycleGroup C p (k + 1)) :
    firstChernClassCapChow C k p L (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
      firstChernClassCapOfInvertible C p k L α :=
  rfl

end Stacks.Chow

end
