module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.EtaleMultiplicityOne

/-!
# The flat pullback of a prime cycle along a morphism of relative dimension zero

Let `π : X ⟶ Y` be a flat morphism of relative dimension zero of schemes locally of finite type
over the base of chapter 42, and let `y` be a point of `Y`. The flat pullback `π^*[y]` of the
prime cycle of `y` is supported on the fibre of `π` over `y`, and at a point `ζ` over `y` at which
the maximal ideal of `𝒪_{Y, y}` generates the maximal ideal of `𝒪_{X, ζ}` — for instance a point
at which `π` is étale — its coefficient is one.

In the proof of the moving lemma (Tag 0B1U) `π` is the finite projection `X ⟶ 𝐏^n` of the proof
of Tag 0B0E, `y` is the generic point of `π(Z)`, and `ζ` the generic point of `Z`: then
`π^*[π(Z)] = [Z] + ∑ m_j [Z_j]` with the `Z_j` the other components of `π^{-1}(π(Z))`.

## Main results

* `Stacks.Chow.flatPullback_apply_ne_zero`: a point in the support of a flat pullback lies over
  a point of the support of the cycle.
* `Stacks.Chow.flatPullback_pointCycle_apply_eq_one`: the coefficient one.

## References

* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1U](https://stacks.math.columbia.edu/tag/0B1U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [LocallyOfFiniteType π] [Flat π]
  (hπ : π ≫ sY = sX) (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension π r) (k : ℤ)

/-- **The support of a flat pullback lies over the support of the cycle.** The coefficient of
`π^*α` at `x` is the coefficient of `α` at `π x` times a multiplicity. -/
public theorem flatPullback_apply_ne_zero (α : CycleGroup C sY k) {x : X}
    (hx : (flatPullback C sX sY π hπ r hr k α).1 x ≠ 0) : α.1 (π.base x) ≠ 0 := by
  rw [flatPullback_apply] at hx
  exact left_ne_zero_of_mul hx

/-- **The flat pullback of a prime cycle has coefficient one at a point where the maximal ideal
extends to the maximal ideal.** Let `π` have relative dimension zero, let `ζ` be a point of `X`
of delta-dimension `k` and suppose the maximal ideal of `𝒪_{Y, π ζ}` generates the maximal ideal
of `𝒪_{X, ζ}`. Then the coefficient of `π^*[π ζ]` at `ζ` is one: the multiplicity of `ζ` in the
scheme-theoretic preimage of the closure of `π ζ` is the length of `𝒪_{X, ζ} / 𝔪_{π ζ} 𝒪_{X, ζ}`,
the residue field. -/
public theorem flatPullback_pointCycle_apply_eq_one (hr0 : AlgebraicGeometry.RelativeDimension π 0)
    (ζ : X) (hζ : relativeDimension C.dimensionFunction sX ζ = k)
    (hy : relativeDimension C.dimensionFunction sY (π.base ζ) = k)
    (hmax : Ideal.map (π.stalkMap ζ).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (π.base ζ))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk ζ)) :
    (flatPullback C sX sY π hπ 0 hr0 k (pointCycle C sY k (π.base ζ) hy)).1 ζ = 1 := by
  classical
  rw [flatPullback_apply, pointCycle_apply, ite_eq_left rfl, one_mul]
  have hdim : relativeDimension C.dimensionFunction sX ζ =
      relativeDimension C.dimensionFunction sY (π.base ζ) + ((0 : ℕ) : ℤ) := by
    rw [hζ, hy]; simp
  have hex := exists_genericPoints_comap_integralComponentAt C sX sY π hπ 0 hr0 ζ hdim
  rw [flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sX π (k + ((0 : ℕ) : ℤ)) ζ
    hex (by rw [hζ]; simp), hmax,
    AlgebraicGeometry.TorFormula.length_quotient_eq_one_of_maximalIdeal_le le_rfl
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
  rfl

end Stacks.Chow

end
