module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ComponentSum

/-!
# Intersecting with the first Chern class of the structure sheaf

The second assertion of Stacks 02SP is that `c₁(𝒪_X) ∩ α = 0` for every `α ∈ Z_{k+1}(X)`, and
the reason is immediate from the construction of the cap product: the global section
`1 ∈ Γ(X, 𝒪_X)` restricts to a nowhere vanishing section of `𝒪_W` on every integral closed
subscheme `W ⊆ X`, so its divisor cycle is zero, so the component rule of Stacks 02SO attached
to `𝒪_X` is the zero rule and the coefficientwise extension of the zero rule is zero.

The vanishing is proved here at the level of generality it is used at: for an arbitrary
`Stacks.Chow.IntegralComponentRule` all of whose component cycles vanish
(`Stacks.Chow.IntegralComponentRule.extendChow_eq_zero`), and then for the cap product of
`Stacks.Chow.trivialChernComponentCycleRule`, the component rule that a nowhere vanishing
section produces.

## Main definitions

* `Stacks.Chow.trivialChernComponentCycleRule` — the component rule of the structure sheaf: the
  divisor cycle of a nowhere vanishing section is zero on every integral component.

## Main results

* `Stacks.Chow.IntegralComponentRule.extendCycleGroup_eq_zero`,
  `Stacks.Chow.IntegralComponentRule.extendChow_eq_zero` — a rule whose component cycles all
  vanish extends to the zero homomorphism.
* `Stacks.Chow.firstChernClassCap_trivialChernComponentCycleRule` — **the second half of Stacks
  02SP**: intersecting with the first Chern class of the structure sheaf is zero.

## Implementation notes

No `@[stacks 02SP]` attribute is placed here. The tag's covering set also contains the
additivity `c₁(L) ∩ α + c₁(N) ∩ α = c₁(L ⊗ N) ∩ α`, which is a statement about the component
rules of three different invertible modules and so is unavailable while the component rule is the
explicit parameter `chern` of
`StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass`; and the statement proved here is about that
parameter rather than about `𝒪_X` itself, since the passage from the sheaf to its component rule
is Stacks 02SJ, which this repository does not have.

## References

* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### A rule with vanishing components extends to zero -/

namespace IntegralComponentRule

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {p : X ⟶ C.S} [LocallyOfFiniteType p]
  {q : Y ⟶ C.S} [LocallyOfFiniteType q] {g : Y ⟶ X} {k : ℤ}
  (R : IntegralComponentRule C p q g k)

/-- A rule on integral components whose cycles all vanish has vanishing totalization. -/
theorem totalize_eq_zero
    (hR : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      R.cycle W hW hDim = 0) (W : X.IdealSheafData) :
    R.totalize W = 0 := by
  classical
  by_cases h : IsIntegral W.subscheme ∧
      schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)
  · rw [R.totalize_eq W h.1 h.2, hR W h.1 h.2]
    rfl
  · rw [totalize, dite_eq_right h]

/-- A rule on integral components whose cycles all vanish extends to the zero homomorphism on
cycle groups: every coefficient of the extension is a locally finite sum of zeros. -/
theorem extendCycleGroup_eq_zero
    (hR : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      R.cycle W hW hDim = 0) :
    R.extendCycleGroup = 0 := by
  ext α y
  rw [extendCycleGroup_apply, ComponentRule.extend_apply]
  change (∑ᶠ x : X, α.1 x * R.totalize (integralComponentAt x) y) = _
  rw [finsum_eq_zero_of_forall_eq_zero fun x ↦ by
    rw [R.totalize_eq_zero hR, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, mul_zero]]
  rfl

/-- A rule on integral components whose cycles all vanish extends to the zero homomorphism to the
Chow group. -/
theorem extendChow_eq_zero
    (hR : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      R.cycle W hW hDim = 0) :
    R.extendChow = 0 := by
  ext α
  rw [extendChow_apply, extendCycleGroup_eq_zero R hR]
  rfl

end IntegralComponentRule

/-! ### The component rule of the structure sheaf -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- The component rule of Stacks 02SO for the structure sheaf `𝒪_X`, with its nowhere vanishing
global section `1`: the divisor cycle of a nowhere vanishing section of `𝒪_W` is zero on every
integral closed subscheme `W ⊆ X`. -/
def trivialChernComponentCycleRule : FirstChernComponentCycleRule C p k := fun _ _ _ ↦ 0

/-- The component cycle on `X` attached to an integral closed subscheme by the rule of the
structure sheaf is zero. -/
@[simp]
theorem firstChernComponentCycle_trivialChernComponentCycleRule (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    firstChernComponentCycle C p k (trivialChernComponentCycleRule C p k) W hW hDim = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change closedSubschemeCyclePushforward C p W 0 x = _
  rw [closedSubschemeCyclePushforward_apply_zero]
  rfl

/-- **Stacks 02SP, second assertion.** Intersecting with the first Chern class of the structure
sheaf is the zero homomorphism `Z_{k+1}(X) ⟶ A_k(X)`.

The global section `1` of `𝒪_X` restricts to a nowhere vanishing section on every integral
closed subscheme `W ⊆ X`, so the component rule of Stacks 02SO for `𝒪_X` is
`Stacks.Chow.trivialChernComponentCycleRule` and the extension of that rule vanishes. -/
theorem firstChernClassCap_trivialChernComponentCycleRule :
    firstChernClassCap C p k (trivialChernComponentCycleRule C p k) = 0 :=
  IntegralComponentRule.extendChow_eq_zero _
    (firstChernComponentCycle_trivialChernComponentCycleRule C p k)

end Stacks.Chow

end
