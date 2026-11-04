module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapProduct
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.ComponentRuleRationalEquivalence

/-!
# A graded rule on integral components determines its extension up to rational equivalence

Let `X` and `Y` be locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `g : Y ⟶ X`. A `Stacks.Chow.GradedIntegralComponentRule C p q g d e` assigns, to
every integral closed subscheme `W ⊆ X` of delta-dimension `d`, an `e`-cycle on `Y` supported
over `W`; its extension `Stacks.Chow.GradedIntegralComponentRule.extendCycleGroup` is the
homomorphism `Z_d(X) → Z_e(Y)` obtained by summing those cycles over the canonical presentation of
a cycle by the integral closed subschemes attached to the points of its support. The rule is
*cycle*-valued, so two rules whose values agree only in the Chow group `A_e(g^{-1} W)` extend to
different cycles. Their extensions nevertheless agree in `A_e(Y)`.

This is `Stacks.Chow.IntegralComponentRule.extendCycleGroup_rationallyEquivalent` for arbitrary
degrees `d` and `e`, instead of a rule taking a subscheme of delta-dimension `k + 1` to a
`k`-cycle.

## Main results

* `Stacks.Chow.GradedIntegralComponentRule.extendCycleGroup_eq_finsum_cycle` — the extension of a
  graded rule is, coefficientwise, the locally finite sum of its values on the canonical
  presentation.
* `Stacks.Chow.GradedIntegralComponentRule.extendCycleGroup_finsum` — the extension of a graded
  rule commutes with locally finite sums.
* `Stacks.Chow.GradedIntegralComponentRule.extendCycleGroup_rationallyEquivalent` — two graded
  rules on integral components taking values rationally equivalent within `g^{-1} W` on every
  integral closed subscheme `W` of delta-dimension `d` extend to rationally equivalent cycles.
* `Stacks.Chow.GradedIntegralComponentRule.extendChow_congr` — the two induced homomorphisms
  `Z_d(X) → A_e(Y)` are equal.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (q : Y ⟶ C.S) [LocallyOfFiniteType q] (g : Y ⟶ X) (d e : ℤ)

/-- An integer multiple of the cycle a graded rule attaches to an integral closed subscheme is
supported over that subscheme. -/
theorem GradedIntegralComponentRule.support_zsmul_cycle_subset
    (R : GradedIntegralComponentRule C p q g d e) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)) (n : ℤ) :
    Function.support (n • R.cycle W hW hDim).1 ⊆ g.base ⁻¹' (W.support : Set X) := by
  refine fun y hy ↦ R.support_subset W hW hDim fun h ↦ hy ?_
  simp [h]

/-- **The component formula on the canonical presentation, for a graded rule.** The extension of a
graded rule on integral components is, coefficientwise, the locally finite sum over the points of
the support of the cycle of the multiples of the cycles the rule attaches to the corresponding
components. -/
theorem GradedIntegralComponentRule.extendCycleGroup_eq_finsum_cycle
    (R : GradedIntegralComponentRule C p q g d e) (β : CycleGroup C p d) (y : Y) :
    (R.extendCycleGroup β).1 y = ∑ᶠ i : cycleSupportIndex β,
      (β.1 i.1 • R.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
        (schemeDeltaDimension_cycleSupportIndex β i)).1 y := by
  rw [R.extendCycleGroup_apply_of_presentation
    (fun i : cycleSupportIndex β ↦ integralComponentAt i.1)
    (fun i ↦ isIntegral_integralComponentAt i.1)
    (fun i ↦ schemeDeltaDimension_cycleSupportIndex β i)
    (locallyFinite_support_integralComponentAt β) (fun i ↦ β.1 i.1) β
    (fun x ↦ cycle_eq_finsum_primeCycles β x) y]
  exact finsum_congr fun _ ↦ rfl

/-- **Extending a graded rule on integral components over a locally finite sum.** If a `d`-cycle
`α` is coefficientwise the locally finite sum of the `d`-cycles `A j`, then the induced
homomorphism `Z_d(X) → Z_e(Y)` of a graded rule on integral components takes `α` to the locally
finite sum of the values it takes on the `A j`. -/
theorem GradedIntegralComponentRule.extendCycleGroup_finsum
    (R : GradedIntegralComponentRule C p q g d e)
    {J : Type*} (A : J → CycleGroup C p d) (E : J → Set X) (hE : LocallyFinite E)
    (hAE : ∀ j, Function.support (A j).1 ⊆ E j) (α : CycleGroup C p d)
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, (A j).1 x) (y : Y) :
    (R.extendCycleGroup α).1 y = ∑ᶠ j : J, (R.extendCycleGroup (A j)).1 y :=
  R.toComponentRule.extendCoeff_finsum (fun j ↦ (A j).1) E hE hAE α.1 hα y

/-- **The extension of a graded rule on integral components is determined up to rational
equivalence by the classes of its values.** If two graded rules on integral components take values
whose difference is rationally equivalent to zero within `g^{-1} W` on every integral closed
subscheme `W ⊆ X` of delta-dimension `d`, then for every `d`-cycle the two extended `e`-cycles on
`Y` are rationally equivalent. -/
theorem GradedIntegralComponentRule.extendCycleGroup_rationallyEquivalent
    (R R' : GradedIntegralComponentRule C p q g d e)
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)),
      IsRationallyEquivalentToZeroWithin C q e
        (R.cycle W hW hDim - R'.cycle W hW hDim) (g.base ⁻¹' (W.support : Set X)))
    (α : CycleGroup C p d) :
    RationallyEquivalent C q e (R.extendCycleGroup α) (R'.extendCycleGroup α) := by
  have hE : LocallyFinite fun i : cycleSupportIndex α ↦
      g.base ⁻¹' ((integralComponentAt i.1).support : Set X) :=
    GysinChernCap.locallyFinite_preimage (locallyFinite_support_integralComponentAt α)
      g.continuous
  have hfin : ∀ (S : GradedIntegralComponentRule C p q g d e) (y : Y),
      (Function.support fun i : cycleSupportIndex α ↦
        (α.1 i.1 • S.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
          (schemeDeltaDimension_cycleSupportIndex α i)).1 y).Finite := fun S y ↦
    finite_support_of_locallyFinite _ hE _
      (fun i ↦ GradedIntegralComponentRule.support_zsmul_cycle_subset C p q g d e S _ _ _ _) y
  show IsRationallyEquivalentToZero C q e (R.extendCycleGroup α - R'.extendCycleGroup α)
  refine rationallyEquivalentToZero_finsum C q e
    (fun i : cycleSupportIndex α ↦ α.1 i.1 •
      (R.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
          (schemeDeltaDimension_cycleSupportIndex α i) -
        R'.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
          (schemeDeltaDimension_cycleSupportIndex α i)))
    _ hE (fun i ↦ isRationallyEquivalentToZeroWithin_zsmul C q e
      (h (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
        (schemeDeltaDimension_cycleSupportIndex α i)) (α.1 i.1) fun _ ↦ rfl) fun y ↦ ?_
  have hsub : (R.extendCycleGroup α - R'.extendCycleGroup α).1 y =
      (R.extendCycleGroup α).1 y - (R'.extendCycleGroup α).1 y := rfl
  rw [hsub, GradedIntegralComponentRule.extendCycleGroup_eq_finsum_cycle C p q g d e R α y,
    GradedIntegralComponentRule.extendCycleGroup_eq_finsum_cycle C p q g d e R' α y,
    ← finsum_sub_distrib (hfin R y) (hfin R' y)]
  refine finsum_congr fun i ↦ ?_
  rw [smul_sub]
  rfl

/-- **The homomorphism to the Chow group is determined by the classes of a graded rule.** Two
graded rules on integral components whose values differ by a cycle rationally equivalent to zero
within `g^{-1} W` on every integral closed subscheme `W ⊆ X` of delta-dimension `d` induce the
same homomorphism `Z_d(X) → A_e(Y)`. -/
theorem GradedIntegralComponentRule.extendChow_congr
    (R R' : GradedIntegralComponentRule C p q g d e)
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)),
      IsRationallyEquivalentToZeroWithin C q e
        (R.cycle W hW hDim - R'.cycle W hW hDim) (g.base ⁻¹' (W.support : Set X)))
    (α : CycleGroup C p d) :
    R.extendChow α = R'.extendChow α :=
  QuotientAddGroup.eq_iff_sub_mem.2
    (GradedIntegralComponentRule.extendCycleGroup_rationallyEquivalent C p q g d e R R' h α)

end Stacks.Chow

end
