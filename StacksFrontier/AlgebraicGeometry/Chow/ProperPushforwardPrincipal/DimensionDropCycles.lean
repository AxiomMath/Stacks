module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cycles and delta-dimensions at the generic point

This file relates the coefficients of `k`-cycles to relative dimensions of points: a `k`-cycle
is supported on points of relative dimension `k`, it vanishes on an integral scheme of
delta-dimension less than `k`, and the proper pushforward of a principal divisor along a
morphism of integral schemes dropping delta-dimension by one is supported at the generic point
of the target. It also proves `dim_δ(Y) ≤ dim_δ(X)` for a dominant morphism `X ⟶ Y` of integral
schemes.

## Main results

* `Stacks.Chow.relativeDimension_eq_of_cycleGroup_apply_ne_zero` — a point carrying a nonzero
  coefficient of a `k`-cycle has relative dimension `k`.
* `Stacks.Chow.eq_zero_of_schemeDeltaDimension_lt` — a `k`-cycle on an integral scheme of
  delta-dimension less than `k` is zero.
* `Stacks.Chow.properPushforward_apply_of_relativeDimension_eq` — at a point of the target of
  relative dimension `k`, the pushforward coefficient is the sum of the coefficients above it
  weighted by residue degrees.
* `Stacks.Chow.schemeDeltaDimension_le_of_isDominant` — for a dominant morphism of integral
  schemes over the base the delta-dimension of the target is at most that of the source.
* `Stacks.Chow.properPushforward_principalDivisorCycle_apply_eq_zero_of_ne_genericPoint` — if
  `dim_δ(Y) = n - 1` then the pushforward to `Y` of a principal divisor from a source of
  delta-dimension `n` vanishes away from the generic point of `Y`.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 0CC1](https://stacks.math.columbia.edu/tag/0CC1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Cycles see relative dimensions -/

/-- A point carrying a nonzero coefficient of a `k`-cycle has relative dimension `k`. -/
theorem relativeDimension_eq_of_cycleGroup_apply_ne_zero (C : ChowSituation.{u})
    {X : Scheme.{u}} (s : X ⟶ C.S) [LocallyOfFiniteType s] (k : ℤ) (c : CycleGroup C s k)
    {x : X} (hx : c.1 x ≠ 0) : relativeDimension C.dimensionFunction s x = k :=
  (mem_cyclesOfDimension_iff_forall_point C s k c.1).mp c.2 x hx

/-- A non-generic point of an integral scheme has strictly smaller relative dimension than the
generic point. -/
private theorem relativeDimension_lt_genericPoint {C : ChowSituation.{u}} {X : Scheme.{u}}
    (s : X ⟶ C.S) [LocallyOfFiniteType s] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X) :
    relativeDimension C.dimensionFunction s x <
      relativeDimension C.dimensionFunction s (genericPoint X) := by
  simpa only [deltaDimensionFunction_apply] using
    (deltaDimensionFunction C s).strictAnti_specializes (genericPoint_specializes x) hx.symm

/-- A `k`-cycle on an integral scheme whose delta-dimension is strictly less than `k` is
zero. -/
theorem eq_zero_of_schemeDeltaDimension_lt (C : ChowSituation.{u}) {X : Scheme.{u}}
    (s : X ⟶ C.S) [LocallyOfFiniteType s] [IsIntegral X] (k : ℤ)
    (hlt : schemeDeltaDimension C s < (k : EInt)) (c : CycleGroup C s k) : c = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  by_contra hx
  have hpoint := relativeDimension_eq_of_cycleGroup_apply_ne_zero C s k c hx
  have hgen : relativeDimension C.dimensionFunction s (genericPoint X) < k := by
    refine WithBotTop.coe_lt_coe.mp ?_
    rwa [← schemeDeltaDimension_eq_genericPoint C s]
  by_cases hxgen : x = genericPoint X
  · subst hxgen
    omega
  · have := relativeDimension_lt_genericPoint (C := C) s hxgen
    omega

/-! ### The pushforward coefficient with the dimension condition discharged -/

/-- At a point of the target whose relative dimension is `k`, the coefficient of the proper
pushforward of a `k`-cycle is the sum of the coefficients above it weighted by residue
degrees. -/
theorem properPushforward_apply_of_relativeDimension_eq (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (c : CycleGroup C sX k) (y : Y)
    (hy : relativeDimension C.dimensionFunction sY y = k) :
    (properPushforward C sX sY p hp k c).1 y =
      ∑ᶠ x ∈ p.base ⁻¹' {y}, c.1 x * (p.residueDegree x : ℤ) := by
  rw [properPushforward_apply]
  refine finsum_congr fun x ↦ finsum_congr fun hx ↦ ?_
  have hxy : p.base x = y := hx
  by_cases hc : c.1 x = 0
  · rw [hc, zero_mul, zero_mul]
  · rw [relativeDimension_eq_of_cycleGroup_apply_ne_zero C sX k c hc, hxy, hy, ite_eq_left rfl]

/-! ### The delta-dimension drops along a dominant morphism -/

/-- For a dominant morphism `X ⟶ Y` of integral schemes over the base, the delta-dimension of
`Y` is at most that of `X`. -/
@[ega "IV 4.1.2" "(i), special case"]
theorem schemeDeltaDimension_le_of_isDominant (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y) [LocallyOfFiniteType p] [IsDominant p]
    (hp : p ≫ sY = sX) : schemeDeltaDimension C sY ≤ schemeDeltaDimension C sX := by
  have hgen : p.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral p).out 1 2).mp (inferInstance : IsDominant p)
  have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY p (genericPoint X)
  rw [hp, hgen] at hstep
  rw [schemeDeltaDimension_eq_genericPoint C sX, schemeDeltaDimension_eq_genericPoint C sY]
  exact WithBotTop.coe_le_coe.mpr (by omega)

/-! ### A pushed-forward principal divisor lives at the generic point -/

/-- If the target has delta-dimension `n - 1`, the pushforward of a principal divisor from a
source of delta-dimension `n` vanishes at every point of the target other than its generic
point. -/
theorem properPushforward_principalDivisorCycle_apply_eq_zero_of_ne_genericPoint
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = ((n - 1 : ℤ) : EInt))
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (g : X.functionField)
    {y : Y} (hy : y ≠ genericPoint Y) :
    (properPushforward C sX sY p hp (n - 1) (principalDivisorCycle C sX hnX g)).1 y = 0 := by
  by_contra hzero
  have hcoeff : relativeDimension C.dimensionFunction sY y = n - 1 :=
    relativeDimension_eq_of_cycleGroup_apply_ne_zero C sY (n - 1) _ hzero
  have hgen : relativeDimension C.dimensionFunction sY (genericPoint Y) = n - 1 :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sY).symm.trans hnY)
  have := relativeDimension_lt_genericPoint (C := C) sY hy
  omega

end Stacks.Chow

end
