module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula

/-!
# Reading the key formula as a difference of two component sums

The left hand side of the key formula of Stacks 0AYC is the locally finite sum

`∑_i (Z_i → X)_* (ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i))`,

and the way chapter 42 consumes it is by recognising the two halves of this expression as the
two cycles it wants to compare: `c₁(N) ∩ div_L(s)` and `c₁(L) ∩ div_N(t)`. This file performs
that recognition. A closed immersion transports a coefficient from a point of the subscheme to
its image and kills nothing else, so the pushforward
`Stacks.Chow.closedSubschemeCyclePushforward` is linear coefficientwise; and the two resulting
families are supported on the locally finite family `{Z_i}`, so the sum over `i` splits. The
outcome is `Stacks.Chow.mk_eq_mk_of_keyFormula`: two cycles whose coefficients are the two halves
of the left hand side have the same class in the Chow group.

## Main results

* `Stacks.Chow.closedSubschemeCyclePushforward_apply_zero`,
  `Stacks.Chow.closedSubschemeCyclePushforward_apply_sub_smul` — the pushforward along a closed
  immersion is linear coefficientwise.
* `Stacks.Chow.KeyFormulaData.finite_support_componentPushforward` — at a fixed point of `X` only
  finitely many members of the family contribute.
* `Stacks.Chow.KeyFormulaData.leftCoeff_eq_sub` — the coefficients of the left hand side of the
  key formula are the difference of the two component sums.
* `Stacks.Chow.mk_eq_mk_of_keyFormula` — two cycles presented by those two component sums have
  the same Chow class, granting the key formula.

## References

* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Coefficientwise linearity of the pushforward along a closed immersion -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)

/-- The pushforward along a closed immersion is linear coefficientwise: at a point in the image
it transports the coefficient of the unique preimage, and away from the image every pushforward
vanishes. -/
private theorem closedSubschemeCyclePushforward_apply_sub_smul_aux (W : X.IdealSheafData)
    (a b : ℤ) (c c' : AlgebraicCycle W.subscheme ℤ) (x : X) :
    closedSubschemeCyclePushforward C p W (a • c - b • c') x =
      a * closedSubschemeCyclePushforward C p W c x -
        b * closedSubschemeCyclePushforward C p W c' x := by
  by_cases hx : x ∈ Set.range W.subschemeι.base
  · obtain ⟨z, rfl⟩ := hx
    rw [closedSubschemeCyclePushforward_apply, closedSubschemeCyclePushforward_apply,
      closedSubschemeCyclePushforward_apply]
    change a • c z - b • c' z = _
    simp
  · rw [closedSubschemeCyclePushforward_apply_of_notMem_range C p W _ hx,
      closedSubschemeCyclePushforward_apply_of_notMem_range C p W c hx,
      closedSubschemeCyclePushforward_apply_of_notMem_range C p W c' hx]
    ring

/-- The pushforward of the zero cycle along a closed immersion is zero. -/
@[simp]
theorem closedSubschemeCyclePushforward_apply_zero (W : X.IdealSheafData) (x : X) :
    closedSubschemeCyclePushforward C p W 0 x = 0 := by
  simpa using closedSubschemeCyclePushforward_apply_sub_smul_aux C p W 0 0 0 0 x

/-- The pushforward along a closed immersion is linear coefficientwise: at a point in the image
it transports the coefficient of the unique preimage, and away from the image every pushforward
vanishes. -/
theorem closedSubschemeCyclePushforward_apply_sub_smul (W : X.IdealSheafData) (a b : ℤ)
    (c c' : AlgebraicCycle W.subscheme ℤ) (x : X) :
    closedSubschemeCyclePushforward C p W (a • c - b • c') x =
      a * closedSubschemeCyclePushforward C p W c x -
        b * closedSubschemeCyclePushforward C p W c' x :=
  closedSubschemeCyclePushforward_apply_sub_smul_aux C p W a b c c' x

/-! ### Splitting the left hand side of the key formula -/

namespace KeyFormulaData

variable (D : KeyFormulaData X)

/-- At a fixed point of `X` only finitely many members of the family `{Z_i}` contribute to a sum
of cycles pushed forward from the `Z_i`: the family is locally finite and the `i`-th summand is
supported on `Z_i`. -/
theorem finite_support_componentPushforward (a : D.Index → ℤ)
    (c : (i : D.Index) → AlgebraicCycle (D.component i).subscheme ℤ) (x : X) :
    (Function.support fun i ↦
      a i * closedSubschemeCyclePushforward C p (D.component i) (c i) x).Finite :=
  finite_support_of_locallyFinite (fun i ↦ ((D.component i).support : Set X))
    D.locallyFinite_support_component
    (fun i y ↦ a i * closedSubschemeCyclePushforward C p (D.component i) (c i) y)
    (fun i _ hy ↦ support_closedSubschemeCyclePushforward_subset C p (D.component i) (c i)
      (right_ne_zero_of_mul hy)) x

/-- **The left hand side of the key formula, split in two.** Its coefficient at `x` is the
coefficient of `∑_i ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i)` minus that of
`∑_i ord_{B_i}(g_i) (Z_i → X)_* div_{L|Z_i}(s_i|Z_i)`. The first of these is the cycle
representing `c₁(N) ∩ div_L(s)` and the second the cycle representing `c₁(L) ∩ div_N(t)`, which
is how Stacks 02TH and 02TI use the formula. -/
theorem leftCoeff_eq_sub [LocallyOfFiniteType p] (x : X) :
    D.leftCoeff C p x =
      (∑ᶠ i, D.orderL i *
        closedSubschemeCyclePushforward C p (D.component i) (D.restrictedDivisorN i) x) -
      ∑ᶠ i, D.orderN i *
        closedSubschemeCyclePushforward C p (D.component i) (D.restrictedDivisorL i) x := by
  rw [← finsum_sub_distrib
    (D.finite_support_componentPushforward C p D.orderL D.restrictedDivisorN x)
    (D.finite_support_componentPushforward C p D.orderN D.restrictedDivisorL x)]
  exact finsum_congr fun i ↦
    closedSubschemeCyclePushforward_apply_sub_smul C p (D.component i) _ _ _ _ x

end KeyFormulaData

/-! ### The equality of Chow classes the key formula yields -/

/-- **Stacks 0AYC, as Stacks 02TH and 02TI use it.** Granting the key formula, two `k`-cycles
whose coefficients are the two halves of its left hand side — the component sums
`∑_i ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i)` and
`∑_i ord_{B_i}(g_i) (Z_i → X)_* div_{L|Z_i}(s_i|Z_i)` — have the same class in `A_k(X)`.

Their difference is the cycle presented by the left hand side, which
`Stacks.Chow.isRationallyEquivalentToZero_of_keyFormula` exhibits as a locally finite sum of
principal divisors on the `Z_i`. -/
theorem mk_eq_mk_of_keyFormula [LocallyOfFiniteType p] {k : ℤ} (D : KeyFormulaData X)
    (hKey : D.KeyFormula C p)
    (hdim : ∀ i : D.Index,
      schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (u v : CycleGroup C p k)
    (hu : ∀ x : X, u.1 x = ∑ᶠ i,
      D.orderL i * closedSubschemeCyclePushforward C p (D.component i) (D.restrictedDivisorN i) x)
    (hv : ∀ x : X, v.1 x = ∑ᶠ i,
      D.orderN i *
        closedSubschemeCyclePushforward C p (D.component i) (D.restrictedDivisorL i) x) :
    (QuotientAddGroup.mk u : chowGroup C p k) = QuotientAddGroup.mk v := by
  have hre : IsRationallyEquivalentToZero C p k (u - v) :=
    isRationallyEquivalentToZero_of_keyFormula C p D hKey k hdim (u - v) fun x ↦ by
      change u.1 x - v.1 x = _
      rw [hu x, hv x, D.leftCoeff_eq_sub C p x]
  have h0 : (QuotientAddGroup.mk' (rationalEquivalences C p k) (u - v)) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hre
  rw [map_sub, sub_eq_zero] at h0
  exact h0

end Stacks.Chow

end
