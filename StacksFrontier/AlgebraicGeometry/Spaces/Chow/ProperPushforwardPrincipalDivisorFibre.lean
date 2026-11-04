module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSumGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor

/-!
# The pushforward coefficient of a principal divisor, and the fibre over the generic point

Two statements about a dominant morphism `p : X ⟶ Y` of good integral algebraic spaces over the
base of Situation 0EDT:

* the coefficient of `p_* div(f)` at an integral closed subspace `W ⊂ Y` of δ-dimension `n - 1`
  is the sum `∑_{p(x) = η} ord_{Z_x}(f) · [κ(x) : κ(η)]` over the fibre of `|p|` over the generic
  point `η` of `W`;
* for `p` locally quasi-finite the fibre of `|p|` over the generic point of `Y` is the generic
  point of `X` alone.

## Main results

* `deltaDimension_eq_of_principalDivisorCycleCoefficients_ne_zero`: the coefficients of `div(f)`
  are supported in δ-dimension `n - 1`.
* `properPushforwardCoeff_principalDivisorCycleCoefficients_eq_finsum_fibre`: the coefficient of
  `p_* div(f)` as a sum over the fibre of `|p|` over a generic point.
* `eq_genericPoint_of_pointsMap_eq_genericPoint`: a point of `X` over the generic point of `Y` is
  the generic point of `X`.
* `fibre_genericPoint_eq_singleton`: the fibre of `|p|` over the generic point of `Y` is the
  generic point of `X`.

## References

* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Reduction

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hdecX : IsDecentSpace D.site D.base D.base_mem X)

variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]

variable (embX : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
    rationalFunctions D.site D.base D.base_mem hX.1 →+*
      W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdecX)
  (f : rationalFunctions D.site D.base D.base_mem hX.1)
  (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (embX W f))

/-- **The coefficients of `div(f)` are supported in δ-dimension `n - 1`.** An integral closed
subspace of `X` with a nonzero `div(f)`-coefficient is a prime divisor, hence has δ-dimension
`n - 1` by Stacks 0EPZ. -/
theorem deltaDimension_eq_of_principalDivisorCycleCoefficients_ne_zero
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (dX : DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : principalDivisorCycleCoefficients D sX hX hdecX embX f hf Z ≠ 0) :
    deltaDimension D sX Z = n - 1 := by
  have hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 := by
    by_contra hc
    exact hZ (principalDivisorCycleCoefficients_of_codimension_ne_one D sX hX hdecX embX f hf hc)
  exact ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hintX dX hdX hnX Z).out 2 3).mp hcod

/-- **The coefficient of `p_* div(f)` at an integral closed subspace of `Y` of δ-dimension
`n - 1`, as a sum over the fibre of `|p|` over its generic point `η`:**

`∑_{p(x) = η} ord_{Z_x}(f) · [κ(x) : κ(η)]`,

where `Z_x` is the integral closed subspace of `X` with generic point `x`. -/
theorem properPushforwardCoeff_principalDivisorCycleCoefficients_eq_finsum_fibre
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (dX : DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) (p : X ⟶ Y)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hZ' : deltaDimension D sY Z' = n - 1) :
    properCyclePushforwardCoeff D sX hX sY hY p
        (principalDivisorCycleCoefficients D sX hX hdecX embX f hf) Z' =
      ∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X p x =
            Z'.ambientGenericPoint D.site D.base D.base_mem ∧
          principalDivisorCycleCoefficients D sX hX hdecX embX f hf
            (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
              (D.isDecentSpace_of_isGood sX hX) x) ≠ 0},
        principalDivisorCycleCoefficients D sX hX hdecX embX f hf
            (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
              (D.isDecentSpace_of_isGood sX hX) x) *
          (cycleResidueDegree D sX hX sY hY p x : ℤ) :=
  finsum_mul_properCycleMult_eq_finsum_fibre D sX hX sY hY p (n - 1)
    (principalDivisorCycleCoefficients D sX hX hdecX embX f hf)
    (deltaDimension_eq_of_principalDivisorCycleCoefficients_ne_zero D sX hX hdecX embX f hf
      hintX dX hdX hnX) Z' hZ'

end Reduction

/-! ### The fibre over the generic point of the target -/

section GenericFibrePoints

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (dX : DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x)

include dX hdX in
/-- **A point of `X` over the generic point of `Y` is the generic point of `X`.** In
Situation 0EDT let `X/B` and `Y/B` be good and integral and let `p : X ⟶ Y` be a locally
quasi-finite dominant morphism over the base. Then the only point of `X` which `|p|` carries to
the generic point of `Y` is the generic point of `X`. -/
theorem eq_genericPoint_of_pointsMap_eq_genericPoint {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hqf : IsLocallyQuasiFinite D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY)
    {x : points D.site D.base D.base_mem X}
    (hx : pointsMap D.site D.base D.base_mem X p x =
      genericPoint D.site D.base D.base_mem hY.1 hintY) :
    x = genericPoint D.site D.base D.base_mem hX.1 hintX := by
  have hcomp : ∀ z : points D.site D.base D.base_mem X,
      D.deltaValue sX z = D.deltaValue sY (pointsMap D.site D.base D.base_mem X p z) := by
    intro z
    rw [← hpB]
    exact D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 p sY hqf hY.2.2 z
  by_contra hne
  have hspec : genericPoint D.site D.base D.base_mem hX.1 hintX ⤳ x :=
    (isGenericPoint_genericPoint D.site D.base D.base_mem hX.1 hintX).specializes
      (Set.mem_univ x)
  have hlt := dX.strictAnti_specializes hspec (Ne.symm hne)
  rw [hdX, hdX, hcomp x, hcomp (genericPoint D.site D.base D.base_mem hX.1 hintX), hx,
    hgen] at hlt
  exact lt_irrefl _ hlt

include dX hdX in
/-- **The fibre of `|p|` over the generic point of `Y` is the generic point of `X`.** In the
setting of `AlgebraicGeometry.Space.eq_genericPoint_of_pointsMap_eq_genericPoint`, the set of
points of `X` which `|p|` carries to the generic point of `Y` is the singleton of the generic
point of `X`. -/
theorem fibre_genericPoint_eq_singleton {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hqf : IsLocallyQuasiFinite D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY) :
    {x : points D.site D.base D.base_mem X | pointsMap D.site D.base D.base_mem X p x =
        genericPoint D.site D.base D.base_mem hY.1 hintY} =
      {genericPoint D.site D.base D.base_mem hX.1 hintX} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨hgen, fun _ hx =>
    eq_genericPoint_of_pointsMap_eq_genericPoint D sX hX sY hY hintX hintY dX hdX hpB hqf hgen hx⟩

end GenericFibrePoints

end AlgebraicGeometry.Space

end
