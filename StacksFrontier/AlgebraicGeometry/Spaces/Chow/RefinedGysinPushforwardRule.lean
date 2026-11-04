module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinPushforwardCap

/-!
# The pushforward of the refined Gysin map as a cap product

In Situation 0EDT let `X/B` be good, `ℒ` an invertible `𝒪_X`-module with a global section `s`,
`E = Z(s)` and `i : E → X`. The refined Gysin map `i^*` of Stacks 0ER1 is defined one integral
closed subspace `W ⊆ X` at a time, and so is `i_* i^*`: on `[W]` it is the pushforward to `X`
of the cycle `div_{ℒ|_W}(t_W)` of clause (1)(b) when `W ⊆ E`, and of the cycle
`[W ×_X E]_k` on `W` when `W ⊄ E` (clause (1)(a), read on `W`). These cycles on the subspaces
`W` form a component rule of Stacks 0EQJ for `ℒ`, and `i_* i^*` is, at the level of cycles, the
cap product with that rule. By Stacks 0EQF, `[W ×_X E]_k = div_{ℒ|_W}(s|_W)`, so each component
is the Weil divisor of a regular meromorphic section of `ℒ|_W`.

## Main definitions

* `AlgebraicGeometry.Space.sectionGysinPushforwardRule`: the component rule `W ↦ i_* i^*[W]`,
  read on `W`.

## Main results

* `AlgebraicGeometry.Space.closedSubspaceCyclePushforward_gysinComponentCycle_sectionGysinRule`:
  `i_*` of the component cycle of `i^*` at `W` is the component cycle of the rule.
* `AlgebraicGeometry.Space.closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule`:
  `i_* i^* α = c₁ ∩ α` at the level of cycles, for the cap product with the rule.

## References

* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER4](https://stacks.math.columbia.edu/tag/0ER4)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (hL : IsInvertibleSheaf D p hp L)
    (s : L.sections) (k : ℤ)

/-- **The component rule of `i_* i^*`.** For an integral closed subspace `W ⊆ X` of
δ-dimension `k + 1`: the cycle `div_{ℒ|_W}(t_W)` of clause (1)(b) of Stacks 0ER1 when
`W ⊆ Z(s)`, and the cycle `[W ×_X Z(s)]_k` of Stacks 0EE9 on `W` when `W ⊄ Z(s)`. -/
def sectionGysinPushforwardRule : FirstChernComponentCycleRule D p k := fun W hW =>
  if hWE : W.subspace ≤ (vanishingLocus D p hp L s).1 then
    restrictedDivisorCycle D p hp L k hL W hW
  else
    closedSubspaceCycle D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
      ((vanishingLocus D p hp L s).1.preimage W.subspace.ι)
      (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι
        (vanishingLocus D p hp L s).1 hp.1 W.isClosedSubspace.1 (vanishingLocus D p hp L s).2)
      k (deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D p hp
        (vanishingLocus D p hp L s) W (isGood_integralClosedSubspace D p hp W) k hW hWE)

/-- For `W ⊆ Z(s)`, the rule `AlgebraicGeometry.Space.sectionGysinPushforwardRule` at `W` is the
cycle `div_{ℒ|_W}(t_W)`. -/
theorem sectionGysinPushforwardRule_of_le {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1) :
    sectionGysinPushforwardRule D p hp L hL s k W hW = restrictedDivisorCycle D p hp L k hL W hW :=
  dite_eq_left hWE

/-- For `W ⊄ Z(s)`, the rule `AlgebraicGeometry.Space.sectionGysinPushforwardRule` at `W` is the
cycle `[W ×_X Z(s)]_k` on `W`. -/
theorem sectionGysinPushforwardRule_of_not_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    sectionGysinPushforwardRule D p hp L hL s k W hW =
      closedSubspaceCycle D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        ((vanishingLocus D p hp L s).1.preimage W.subspace.ι)
        (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι
          (vanishingLocus D p hp L s).1 hp.1 W.isClosedSubspace.1 (vanishingLocus D p hp L s).2)
        k (deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D p hp
          (vanishingLocus D p hp L s) W (isGood_integralClosedSubspace D p hp W) k hW hWE) :=
  dite_eq_right hWE

/-- **`i_* i^*[W]` is the component cycle of the rule at `W`.** -/
theorem closedSubspaceCyclePushforward_gysinComponentCycle_sectionGysinRule
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    closedSubspaceCyclePushforward D p hp (vanishingLocus D p hp L s) k
        (gysinComponentCycle D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL) W) =
      firstChernComponentCycle D p hp k (sectionGysinPushforwardRule D p hp L hL s k) W := by
  by_cases hW : deltaDimension D p W = k + 1
  · rw [firstChernComponentCycle_of_deltaDimension_eq D p hp k _ hW]
    by_cases hWE : W.subspace ≤ (vanishingLocus D p hp L s).1
    · rw [gysinComponentCycle_of_le D p _ _ k _ hW hWE, sectionGysinPushforwardRule_of_le D p hp L
        hL s k hW hWE, closedSubspaceCyclePushforward_containedPushforward D p hp _ k
        (isGood_vanishingLocus D p hp L s) hWE]
      rfl
    · rw [gysinComponentCycle_of_not_le D p _ _ k _ hW hWE, sectionGysinPushforwardRule_of_not_le
        D p hp L hL s k hW hWE,
        integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq_gysinIntersectionCycle D p
          hp (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) W
          (isGood_integralClosedSubspace D p hp W) k hW hWE]
      rfl
  · rw [gysinComponentCycle_of_deltaDimension_ne D p _ _ k _ hW,
      firstChernComponentCycle_of_deltaDimension_ne D p hp k _ hW, map_zero]

/-- **`i_* i^* α = c₁ ∩ α` at the level of cycles**, for the cap product of Stacks 0EQJ with the
component rule `AlgebraicGeometry.Space.sectionGysinPushforwardRule`. -/
theorem closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule
    (α : CycleGroup D p (k + 1)) :
    closedSubspaceCyclePushforward D p hp (vanishingLocus D p hp L s) k
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL) α) =
      firstChernCapCycleMap D p hp k (sectionGysinPushforwardRule D p hp L hL s k) α := by
  refine Subtype.ext (funext fun V => ?_)
  rw [closedSubspaceCyclePushforward_gysinCycleMap_apply, firstChernCapCycleMap_apply]
  refine finsum_congr fun W => ?_
  rw [closedSubspaceCyclePushforward_gysinComponentCycle_sectionGysinRule]

end AlgebraicGeometry.Space

end
