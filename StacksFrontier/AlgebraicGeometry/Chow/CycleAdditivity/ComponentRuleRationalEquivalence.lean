module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionGysinRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapInvertible

/-!
# A rule on integral components determines its extension up to rational equivalence

Let `X` and `Y` be locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `g : Y ⟶ X`. A `Stacks.Chow.IntegralComponentRule` assigns, to every integral
closed subscheme `W ⊆ X` of delta-dimension `k + 1`, a `k`-cycle on `Y` supported over `W`; its
extension `Stacks.Chow.IntegralComponentRule.extendCycleGroup` is the homomorphism
`Z_{k+1}(X) → Z_k(Y)` obtained by summing those cycles over the canonical presentation of a cycle
by the integral closed subschemes attached to the points of its support. The rule is
*cycle*-valued, so two rules whose values agree only in the Chow group `A_k(g^{-1} W)` extend to
different cycles. Their extensions nevertheless agree in `A_k(Y)`.

This generalises `Stacks.Chow.firstChernCapRule_extendCycleGroup_rationallyEquivalent` from the
rule of Stacks 02SO to an arbitrary rule on integral components, with the hypothesis that the
values are rationally equivalent within `g^{-1} W` rather than on `W`.

## Main results

* `Stacks.Chow.IntegralComponentRule.extendCycleGroup_rationallyEquivalent` — two rules on
  integral components taking values rationally equivalent within `g^{-1} W` on every integral
  closed subscheme `W` of delta-dimension `k + 1` extend to rationally equivalent cycles.
* `Stacks.Chow.IntegralComponentRule.extendChow_congr` — the two induced homomorphisms
  `Z_{k+1}(X) → A_k(Y)` are equal.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (q : Y ⟶ C.S) [LocallyOfFiniteType q] (g : Y ⟶ X) (k : ℤ)

/-- If two rules on integral components take values whose difference is rationally equivalent to
zero within `g^{-1} W` on every integral closed subscheme `W ⊆ X` of delta-dimension `k + 1`, then
for every `(k+1)`-cycle the two extended `k`-cycles on `Y` are rationally equivalent. -/
theorem IntegralComponentRule.extendCycleGroup_rationallyEquivalent
    (R R' : IntegralComponentRule C p q g k)
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      IsRationallyEquivalentToZeroWithin C q k
        (R.cycle W hW hDim - R'.cycle W hW hDim) (g.base ⁻¹' (W.support : Set X)))
    (α : CycleGroup C p (k + 1)) :
    RationallyEquivalent C q k (R.extendCycleGroup α) (R'.extendCycleGroup α) := by
  have hE : LocallyFinite fun i : cycleSupportIndex α ↦
      g.base ⁻¹' ((integralComponentAt i.1).support : Set X) :=
    GysinChernCap.locallyFinite_preimage (locallyFinite_support_integralComponentAt α)
      g.continuous
  have hfin : ∀ (S : IntegralComponentRule C p q g k) (y : Y),
      (Function.support fun i : cycleSupportIndex α ↦
        (α.1 i.1 • S.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
          (schemeDeltaDimension_cycleSupportIndex α i)).1 y).Finite := fun S y ↦
    finite_support_of_locallyFinite _ hE _
      (fun i ↦ GysinChernCap.support_zsmul_cycle_subset C p q g S _ _ _ _) y
  change IsRationallyEquivalentToZero C q k (R.extendCycleGroup α - R'.extendCycleGroup α)
  refine rationallyEquivalentToZero_finsum C q k
    (fun i : cycleSupportIndex α ↦ α.1 i.1 •
      (R.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
          (schemeDeltaDimension_cycleSupportIndex α i) -
        R'.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
          (schemeDeltaDimension_cycleSupportIndex α i)))
    _ hE (fun i ↦ isRationallyEquivalentToZeroWithin_zsmul C q k
      (h (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
        (schemeDeltaDimension_cycleSupportIndex α i)) (α.1 i.1) fun _ ↦ rfl) fun y ↦ ?_
  have hsub : (R.extendCycleGroup α - R'.extendCycleGroup α).1 y =
      (R.extendCycleGroup α).1 y - (R'.extendCycleGroup α).1 y := rfl
  rw [hsub, GysinChernCap.extendCycleGroup_eq_finsum_cycle C p q g R α y,
    GysinChernCap.extendCycleGroup_eq_finsum_cycle C p q g R' α y,
    ← finsum_sub_distrib (hfin R y) (hfin R' y)]
  refine finsum_congr fun i ↦ ?_
  rw [smul_sub]
  rfl

/-- Two rules on integral components whose values differ by a cycle rationally equivalent to zero
within `g^{-1} W` on every integral closed subscheme `W ⊆ X` of delta-dimension `k + 1` induce the
same homomorphism `Z_{k+1}(X) → A_k(Y)`. -/
theorem IntegralComponentRule.extendChow_congr (R R' : IntegralComponentRule C p q g k)
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      IsRationallyEquivalentToZeroWithin C q k
        (R.cycle W hW hDim - R'.cycle W hW hDim) (g.base ⁻¹' (W.support : Set X)))
    (α : CycleGroup C p (k + 1)) :
    R.extendChow α = R'.extendChow α :=
  QuotientAddGroup.eq_iff_sub_mem.2
    (IntegralComponentRule.extendCycleGroup_rationallyEquivalent C p q g k R R' h α)

end Stacks.Chow

end
