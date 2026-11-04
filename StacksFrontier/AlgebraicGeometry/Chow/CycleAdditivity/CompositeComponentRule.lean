module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.ComponentRuleFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocallyFinitePreimage

/-!
# Composing two rules on integral components

For rules on integral components `R₁` over `g : Y ⟶ X` and `R₂` over `h : Z ⟶ Y`, the composite
of their coefficientwise extensions `Stacks.Chow.IntegralComponentRule.extendCycleGroup`,
evaluated on a cycle with a locally finite presentation `∑ n_j [W_j]`, is the locally finite sum
of the values of the outer extension on the cycles the inner rule attaches to the `W_j`.

## Main results

* `Stacks.Chow.IntegralComponentRule.extendCycleGroup_comp_of_presentation` — the composite of
  two rules on integral components, evaluated on a locally finite presentation.

## References

* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02R9](https://stacks.math.columbia.edu/tag/02R9)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {X Y Z : Scheme.{u}} {p : X ⟶ C.S} [LocallyOfFiniteType p]
  {q : Y ⟶ C.S} [LocallyOfFiniteType q] {r : Z ⟶ C.S} [LocallyOfFiniteType r]
  {g : Y ⟶ X} {h : Z ⟶ Y} {k : ℤ}

/-- **The composite of two rules on integral components, read off a locally finite
presentation.** If a `(k+2)`-cycle `α` on `X` is presented as the locally finite sum
`∑ n_j [W_j]` by integral closed subschemes of delta-dimension `k + 2`, then applying the inner
rule and then the outer one gives the locally finite sum of the values of the outer rule's
extension on the cycles the inner rule attaches to the `W_j`. -/
theorem IntegralComponentRule.extendCycleGroup_comp_of_presentation
    (R₁ : IntegralComponentRule C p q g (k + 1)) (R₂ : IntegralComponentRule C q r h k)
    {J : Type u} (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p (k + 1 + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1 + 1)).1 x) (z : Z) :
    (R₂.extendCycleGroup (R₁.extendCycleGroup α)).1 z =
      ∑ᶠ j : J, n j * (R₂.extendCycleGroup (R₁.cycle (W j) (hW j) (hDim j))).1 z := by
  set D : J → CycleGroup C q (k + 1) := fun j ↦ n j • R₁.cycle (W j) (hW j) (hDim j)
  have hsupp (j : J) : Function.support (D j).1 ⊆ g.base ⁻¹' ((W j).support : Set X) :=
    fun _ hy ↦ R₁.support_subset (W j) (hW j) (hDim j) (right_ne_zero_of_mul hy)
  rw [R₂.extendCycleGroup_finsum D _ (hLocal.preimage_continuous g.continuous) hsupp _
    (R₁.extendCycleGroup_apply_of_presentation W hW hDim hLocal n α hα) z]
  exact finsum_congr fun j ↦ congrArg (·.1 z) (map_zsmul R₂.extendCycleGroup (n j) _)

end Stacks.Chow

end
