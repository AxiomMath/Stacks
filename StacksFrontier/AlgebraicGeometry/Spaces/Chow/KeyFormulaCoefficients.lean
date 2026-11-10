module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection

/-!
# Coefficients of the pushed-forward divisors on a prime divisor

In Situation 0EDT let `X/B` be good and let `W ⊆ X` be an integral closed subspace of δ-dimension
`k + 1`. For a `k`-cycle `c` on `W` the coefficient of `(W → X)_* c` at an integral closed
subspace `Y ⊆ X` is `c(Y')` when `Y` is the image of an integral closed subspace `Y'` of `W`, and
zero otherwise. When `c` is the Weil divisor of a regular meromorphic section of an invertible
module on `W`, or the principal divisor of a rational function on `W`, and `Y` has δ-dimension
`k`, the subspace `Y'` is a prime divisor of `W` and `c(Y')` is the order of vanishing there.

## Main results

* `AlgebraicGeometry.Space.integralClosedSubspacePushforward_apply_pushforward` and
  `AlgebraicGeometry.Space.integralClosedSubspacePushforward_apply_of_forall_ne`: the coefficient
  of `(W → X)_* c` at `Y` is `c(Y')` when `Y` is the image of `Y'`, and zero when `Y` is not an
  image.
* `AlgebraicGeometry.Space.codimension_eq_one_of_deltaDimension_pushforward`: `Y'` is a prime
  divisor of `W`.
* `AlgebraicGeometry.Space.canonicalDivisorCycleAt_apply_of_codimension_eq_one` and
  `AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt_apply_of_codimension_eq_one`: the
  coefficients of a Weil divisor and of a principal divisor at a prime divisor are orders of
  vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- The coefficient of a pushforward along `W → X` at the image of an integral closed subspace
`Y'` of `W` is the coefficient at `Y'`. -/
theorem integralClosedSubspacePushforward_apply_pushforward
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) {k : ℤ}
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (Y' : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) :
    (integralClosedSubspacePushforward D sX hX W k c).1
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 Y') = c.1 Y' :=
  cycleClosedPushforward_apply_pushforward D hX.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 c.1 Y'

/-- The coefficient of a pushforward along `W → X` vanishes at an integral closed subspace which
is not the image of one of `W`. -/
theorem integralClosedSubspacePushforward_apply_of_forall_ne
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) {k : ℤ}
    (c : CycleGroup D (W.subspace.ι ≫ sX) k) (Y : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hY : ∀ Y', IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 Y' ≠ Y) :
    (integralClosedSubspacePushforward D sX hX W k c).1 Y = 0 :=
  cycleClosedPushforward_apply_of_forall_ne D hX.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 c.1 Y hY

/-- An integral closed subspace `Y'` of an integral closed subspace `W ⊆ X` of δ-dimension
`k + 1` whose image in `X` has δ-dimension `k` is a prime divisor of `W`. -/
theorem codimension_eq_one_of_deltaDimension_pushforward
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) {k : ℤ}
    (hW : deltaDimension D sX W = k + 1)
    (Y' : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (hY : deltaDimension D sX (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 Y') = k) :
    codimension (integralClosedSubspaceSupport D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W).1 Y') = 1 := by
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hn : deltaDimensionClosed D (W.subspace.ι ≫ sX) hWg Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW]
  have hδ : deltaDimension D (W.subspace.ι ≫ sX) Y' = k + 1 - 1 := by
    rw [← IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 Y', hY, add_sub_cancel_right]
  exact ((isPrimeDivisor_tfae_of_isIntegralSpace D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace
    (deltaDimensionFunction D _ hWg) (deltaDimensionFunction_apply D _ hWg) hn Y').out 2 3).mpr hδ

section Divisors

variable {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- The coefficient of the canonical Weil divisor `div_ℳ(τ)` at a prime divisor (an integral
closed subspace of codimension one) is the order of vanishing of Stacks 0EPR at the canonical
ratio. -/
theorem canonicalDivisorCycleAt_apply_of_codimension_eq_one
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (P : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hP : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 P) = 1) :
    (canonicalDivisorCycleAt D sY hY hintY M hM τ hτ hk).1 P =
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
        W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isGood D sY hY) hintY
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
        W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isGood D sY hY) hintY
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
        W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isGood D sY hY) hintY
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
      orderOfVanishingSection.{u, u} D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY) (P.toPrimeDivisor D.site D.base D.base_mem hY.1 hP) M τ
        ((P.toPrimeDivisor D.site D.base D.base_mem hY.1 hP).canonicalLocalRatio D.site D.base
          D.base_mem hY.1 (isDecentSpace_of_isGood D sY hY) M hM hintY
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)) := by
  have := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
    W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hintY
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  have := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
    W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hintY
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  have := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
    W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hintY
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  exact divisorCycleCoefficients_of_codimension_eq_one D sY hY _ M τ _ hP

/-- The coefficient of the canonical principal divisor `div(f)` at a prime divisor is the order
of vanishing of Stacks 0ENL there. -/
theorem canonicalPrincipalDivisorCycleAt_apply_of_codimension_eq_one
    (f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (P : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hP : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 P) = 1) :
    (canonicalPrincipalDivisorCycleAt D sY hY hintY f hk).1 P =
      ordRationalFunction D.site D.base D.base_mem hY.1 hintY
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) f
        (P.toPrimeDivisor D.site D.base D.base_mem hY.1 hP) := by
  unfold canonicalPrincipalDivisorCycleAt
  simp only
  rw [principalDivisorCycleCoefficients, dite_eq_left hP]
  rfl

end Divisors

end AlgebraicGeometry.Space

end
