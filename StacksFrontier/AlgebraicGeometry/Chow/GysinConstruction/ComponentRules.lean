module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Operations on cycles specified on integral components

Several operations of chapter 42 of the Stacks Project are *defined* by a rule on integral
closed subschemes: the Gysin map of the zero scheme of a section of an invertible module
(Stacks 02T8), intersection with the first Chern class of an invertible module (Stacks 02SO),
the sum of a locally finite family of principal divisors (Stacks 02RW). In each case one is
given, for every integral closed subscheme `W ⊆ X` of delta-dimension `k + 1`, a `k`-cycle on a
scheme `Y` mapping to `X`, supported over `W`; and one wants a homomorphism
`Z_{k+1}(X) → A_k(Y)` whose value on a locally finite presentation `α = ∑ n_j [W_j]` is the
class of `∑ n_j c(W_j)`.

This file constructs that homomorphism from a `Stacks.Chow.IntegralComponentRule`, as
`Stacks.Chow.IntegralComponentRule.extendChow`, and proves the locally finite component formula
`Stacks.Chow.IntegralComponentRule.extendCycleGroup_apply_of_presentation`.

## Main definitions

* `Stacks.Chow.IntegralComponentRule` — a rule on integral closed subschemes of
  delta-dimension `k + 1`, assigning a `k`-cycle on `Y` supported over the subscheme.
* `Stacks.Chow.IntegralComponentRule.extendCycleGroup` — the induced homomorphism
  `Z_{k+1}(X) → Z_k(Y)`.
* `Stacks.Chow.IntegralComponentRule.extendChow` — its composite with the projection to the
  Chow group `A_k(Y)`.

## Main results

* `Stacks.Chow.IntegralComponentRule.extendCycleGroup_apply_of_presentation` — the
  coefficientwise formula on an arbitrary locally finite presentation of a cycle by integral
  closed subschemes.
* `Stacks.Chow.IntegralComponentRule.extendCycleGroup_cycleAssociatedToClosedSubscheme` — the
  value on the fundamental cycle of a single integral closed subscheme.

## References

* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (q : Y ⟶ C.S) [LocallyOfFiniteType q] (g : Y ⟶ X) (k : ℤ)

/-- A *rule on integral components* of delta-dimension `k + 1`, along a morphism `g : Y ⟶ X`:
to every integral closed subscheme `W ⊆ X` of delta-dimension `k + 1` it assigns a `k`-cycle on
`Y` whose support lies over `W`. -/
structure IntegralComponentRule where
  /-- The `k`-cycle on `Y` attached to an integral closed subscheme of delta-dimension `k + 1`. -/
  cycle : ∀ W : X.IdealSheafData, IsIntegral W.subscheme →
    schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) → CycleGroup C q k
  /-- The cycle attached to `W` is supported over `W`. -/
  support_subset : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
    Function.support (cycle W hW hDim).1 ⊆ g.base ⁻¹' (W.support : Set X)

namespace IntegralComponentRule

variable {C p q g k} (R : IntegralComponentRule C p q g k)

/-- The rule extended by zero to every quasi-coherent ideal sheaf of `X`. -/
def totalize (W : X.IdealSheafData) : AlgebraicCycle Y ℤ :=
  open Classical in
  if h : IsIntegral W.subscheme ∧
      schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) then
    (R.cycle W h.1 h.2).1
  else 0

/-- On an integral closed subscheme of delta-dimension `k + 1` the totalized rule is the rule. -/
theorem totalize_eq (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    R.totalize W = (R.cycle W hW hDim).1 := by
  classical
  rw [totalize, dite_eq_left (⟨hW, hDim⟩ : IsIntegral W.subscheme ∧ _)]

/-- A property of cycles holding for `0` and for every cycle of the rule holds for the totalized
rule. -/
private theorem totalize_induction (W : X.IdealSheafData) {P : AlgebraicCycle Y ℤ → Prop}
    (h0 : P 0) (h : ∀ (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      P (R.cycle W hW hDim).1) : P (R.totalize W) := by
  classical
  by_cases hc : IsIntegral W.subscheme ∧
      schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)
  · rw [R.totalize_eq W hc.1 hc.2]
    exact h _ _
  · rw [totalize, dite_eq_right hc]
    exact h0

/-- Every value of the totalized rule is a `k`-cycle. -/
theorem totalize_mem_cyclesOfDimension (W : X.IdealSheafData) :
    R.totalize W ∈ cyclesOfDimension C q k :=
  R.totalize_induction W (cyclesOfDimension C q k).zero_mem fun hW hDim ↦ (R.cycle W hW hDim).2

/-- The totalized rule is supported over the subscheme it is attached to. -/
theorem support_totalize_subset (W : X.IdealSheafData) :
    Function.support (R.totalize W) ⊆ g.base ⁻¹' (W.support : Set X) :=
  R.totalize_induction W (P := fun c ↦ Function.support c ⊆ g.base ⁻¹' (W.support : Set X))
    (by simp) fun hW hDim ↦ R.support_subset W hW hDim

/-- A rule on integral components, read as a rule on points of `X`: the point `x` stands for the
reduced induced closed subscheme on the closure of `x`. -/
def toComponentRule : ComponentRule g.base where
  cycle x := R.totalize (integralComponentAt x)
  mem_closure_of_apply_ne_zero x y hy := by
    have h := R.support_totalize_subset (integralComponentAt x) (by exact hy)
    rwa [Set.mem_preimage, coe_support_integralComponentAt] at h

/-- The cycle the induced rule on points attaches to the generic point of an integral closed
subscheme of delta-dimension `k + 1` is the cycle the original rule attaches to it. -/
theorem toComponentRule_cycle_genericPointOf (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    R.toComponentRule.cycle (genericPointOf W hW) = (R.cycle W hW hDim).1 := by
  change R.totalize (integralComponentAt (genericPointOf W hW)) = _
  rw [integralComponentAt_genericPointOf W hW, R.totalize_eq W hW hDim]

/-- The homomorphism `Z_{k+1}(X) → Z_k(Y)` extending a rule on integral components
coefficientwise. -/
def extendCycleGroup : CycleGroup C p (k + 1) →+ CycleGroup C q k where
  toFun α := ⟨R.toComponentRule.extend g.continuous α.1, by
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro y hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.1
      (R.toComponentRule.support_extend_subset g.continuous α.1 (by exact hy))
    exact (mem_cyclesOfDimension_iff_forall_point C q k _).1
      (R.totalize_mem_cyclesOfDimension (integralComponentAt x)) y (by exact hx)⟩
  map_zero' := Subtype.ext (map_zero (R.toComponentRule.extend g.continuous))
  map_add' α β := Subtype.ext (map_add (R.toComponentRule.extend g.continuous) α.1 β.1)

/-- The coefficient of `R.extendCycleGroup α` at a point `y` is that of the extension of the
induced rule on points applied to `α`. -/
@[simp]
theorem extendCycleGroup_apply (α : CycleGroup C p (k + 1)) (y : Y) :
    (R.extendCycleGroup α).1 y = R.toComponentRule.extend g.continuous α.1 y := rfl

/-- The homomorphism `Z_{k+1}(X) → A_k(Y)` to the Chow group extending a rule on integral
components coefficientwise. -/
def extendChow : CycleGroup C p (k + 1) →+ chowGroup C q k :=
  (QuotientAddGroup.mk' (rationalEquivalences C q k)).comp R.extendCycleGroup

/-- `R.extendChow α` is the class of the cycle `R.extendCycleGroup α` modulo rational
equivalence. -/
@[simp]
theorem extendChow_apply (α : CycleGroup C p (k + 1)) :
    R.extendChow α = QuotientAddGroup.mk (R.extendCycleGroup α) := rfl

/-- **The defining formula.** On a locally finite presentation `α = ∑ n_j [W_j]` of a `(k+1)`-cycle
by integral closed subschemes of delta-dimension `k + 1`, the extension of a rule on integral
components is the locally finite sum of the cycles the rule attaches to the `W_j`, weighted by
the coefficients `n_j`. -/
theorem extendCycleGroup_apply_of_presentation {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) (y : Y) :
    (R.extendCycleGroup α).1 y = ∑ᶠ j : J, n j * (R.cycle (W j) (hW j) (hDim j)).1 y := by
  have hclosure : (fun j ↦ closure {genericPointOf (W j) (hW j)}) =
      fun j ↦ ((W j).support : Set X) :=
    funext fun j ↦ (support_eq_closure_genericPointOf (W j) (hW j)).symm
  have hσ : LocallyFinite fun j ↦ closure {genericPointOf (W j) (hW j)} := by
    rwa [hclosure]
  rw [extendCycleGroup_apply,
    R.toComponentRule.extend_apply_of_presentation g.continuous
      (fun j ↦ genericPointOf (W j) (hW j)) n
      (fun j x ↦ (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x)
      (fun j x hx ↦ by
        by_contra hne
        exact hx (cycleAssociatedToClosedSubscheme_integral_apply_of_ne C p (W j) (hW j)
          (k + 1) hne))
      (fun j ↦ cycleAssociatedToClosedSubscheme_integral_apply C p (W j) (hW j) (hDim j))
      hσ α.1 hα y]
  exact finsum_congr fun j ↦ by
    rw [R.toComponentRule_cycle_genericPointOf (W j) (hW j) (hDim j)]

/-- The value of the extension of a rule on integral components on the fundamental cycle of a
single integral closed subscheme of delta-dimension `k + 1` is the cycle the rule attaches to
it. -/
theorem extendCycleGroup_cycleAssociatedToClosedSubscheme (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    R.extendCycleGroup (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      R.cycle W hW hDim := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [R.extendCycleGroup_apply_of_presentation (fun _ : PUnit.{u + 1} ↦ W) (fun _ ↦ hW)
    (fun _ ↦ hDim) (fun _ ↦ ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩) (fun _ ↦ 1) _
    (fun x ↦ by simp [finsum_unique]) y]
  simp [finsum_unique]

end IntegralComponentRule

/-- The coefficient of a sum of two `k`-cycles at a point is the sum of the two coefficients. -/
public theorem cycleGroup_add_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (a b : CycleGroup C f k) (y : X) :
    (a + b).1 y = a.1 y + b.1 y :=
  rfl

end Stacks.Chow

end
