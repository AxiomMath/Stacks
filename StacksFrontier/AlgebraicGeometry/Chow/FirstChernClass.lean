module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.WeilDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction

/-!
# Intersecting with the first Chern class of an invertible module

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `L` be an invertible module on `X`. Stacks 02SO constructs an additive cap
product

  `Z_{k+1}(X) ⟶ A_k(X)`,  `α ↦ c₁(L) ∩ α`,

by prescribing it on integral components: an integral closed subscheme `W ⊆ X` of
delta-dimension `k + 1` is sent to the pushforward to `X` of a cycle representing the first Chern
class of `L|_W` capped with the fundamental cycle of `W`, and the rule is extended
coefficientwise over an arbitrary locally finite presentation of a `(k+1)`-cycle. Here the
extension is `Stacks.Chow.IntegralComponentRule.extendChow` with `Y = X` and `g = 𝟙 X`, and the
component cycle is an explicit parameter `chern`.

## Main definitions

* `Stacks.Chow.FirstChernComponentCycleRule` — a `k`-cycle on each integral closed subscheme of
  delta-dimension `k + 1`.
* `Stacks.Chow.firstChernComponentCycle` — the cycle on `X` attached to an integral component.
* `Stacks.Chow.firstChernCapRule` — that rule packaged as an
  `Stacks.Chow.IntegralComponentRule`.
* `Stacks.Chow.IsFirstChernClassCap` — the locally finite component formula characterising the
  cap product.
* `Stacks.Chow.firstChernClassCapConstruction`, `Stacks.Chow.firstChernClassCap` — the cap
  product, with and without that formula.

## Main results

* `Stacks.Chow.firstChernClassCap_integral_cycle` — the value on the fundamental cycle of a
  single integral closed subscheme.
* `Stacks.Chow.firstChernClassCap_finsum` — the locally finite component formula.

## References

* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The component input -/

/-- A choice, for every integral closed subscheme `W ⊆ X` of delta-dimension `k + 1`, of a
`k`-cycle on `W`. -/
abbrev FirstChernComponentCycleRule (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) : Type u :=
  ∀ W : X.IdealSheafData, IsIntegral W.subscheme →
    schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) →
    CycleGroup C (W.subschemeι ≫ p) k

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (chern : FirstChernComponentCycleRule C p k)

/-! ### The component rule -/

/-- **Stacks 02SO.** The cycle on `X` attached to an integral component `W` of delta-dimension
`k + 1`: the pushforward along the closed immersion `W ⟶ X` of the first Chern class cycle
on `W`. -/
def firstChernComponentCycle (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    CycleGroup C p k :=
  properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k (chern W hW hDim)

/-- The component cycle of `W` is supported on `W`. -/
theorem support_firstChernComponentCycle_subset (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    Function.support (firstChernComponentCycle C p k chern W hW hDim).1 ⊆
      (𝟙 X : X ⟶ X).base ⁻¹' (W.support : Set X) := by
  refine (support_properPushforward_subset C (W.subschemeι ≫ p) p W.subschemeι rfl k _).trans ?_
  rw [W.range_subschemeι]
  exact fun _ hx ↦ hx

/-- **Stacks 02SO.** The component rule of the first Chern class cap product, as an
`Stacks.Chow.IntegralComponentRule`. -/
def firstChernCapRule : IntegralComponentRule C p p (𝟙 X) k where
  cycle := firstChernComponentCycle C p k chern
  support_subset := support_firstChernComponentCycle_subset C p k chern

/-! ### The cap product -/

/-- **Stacks 02SO.** The property of an additive map `F` that, on every locally finite
presentation `α = ∑ n_j [W_j]` of a `(k+1)`-cycle, `F α` is the class of the cycle
`∑ n_j c₁(L) ∩ [W_j]`. -/
def IsFirstChernClassCap (F : CycleGroup C p (k + 1) →+ chowGroup C p k) : Prop :=
  ∀ {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (_hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (n : J → ℤ) (α : CycleGroup C p (k + 1)),
    (∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) →
    ∃ β : CycleGroup C p k,
      F α = QuotientAddGroup.mk β ∧
      ∀ x : X, β.1 x = ∑ᶠ j : J, n j *
        (firstChernComponentCycle C p k chern (W j) (hW j) (hDim j)).1 x

/-- **Stacks 02SO.** Construction of the first Chern class cap product, together with its
locally finite component rule. -/
def firstChernClassCapConstruction :
    { F : CycleGroup C p (k + 1) →+ chowGroup C p k // IsFirstChernClassCap C p k chern F } :=
  ⟨(firstChernCapRule C p k chern).extendChow, by
    intro J W hW hDim hLocal n α hα
    exact ⟨(firstChernCapRule C p k chern).extendCycleGroup α, rfl,
      (firstChernCapRule C p k chern).extendCycleGroup_apply_of_presentation W hW hDim hLocal n α
        hα⟩⟩

/-- **Stacks 02SO.** Intersection with the first Chern class of an invertible module. -/
def firstChernClassCap : CycleGroup C p (k + 1) →+ chowGroup C p k :=
  (firstChernClassCapConstruction C p k chern).val

/-- **Stacks 02SO.** On the fundamental cycle of a single integral closed subscheme of
delta-dimension `k + 1` the cap product is the class of the pushforward of the component cycle. -/
theorem firstChernClassCap_integral_cycle (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    firstChernClassCap C p k chern
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      QuotientAddGroup.mk (firstChernComponentCycle C p k chern W hW hDim) := by
  show QuotientAddGroup.mk
    ((firstChernCapRule C p k chern).extendCycleGroup
      (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) = _
  exact congrArg QuotientAddGroup.mk
    ((firstChernCapRule C p k chern).extendCycleGroup_cycleAssociatedToClosedSubscheme W hW hDim)

/-- **Stacks 02SO.** The locally finite component formula for the cap product: on a presentation
`α = ∑ n_j [W_j]` the cap product is the class of `∑ n_j c₁(L) ∩ [W_j]`. -/
theorem firstChernClassCap_finsum {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C p k,
      firstChernClassCap C p k chern α = QuotientAddGroup.mk β ∧
      ∀ x : X, β.1 x = ∑ᶠ j : J, n j *
        (firstChernComponentCycle C p k chern (W j) (hW j) (hDim j)).1 x :=
  (firstChernClassCapConstruction C p k chern).2 W hW hDim hLocal n α hα

end Stacks.Chow

end
