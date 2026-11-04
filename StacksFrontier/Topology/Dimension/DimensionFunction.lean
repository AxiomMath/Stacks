module

public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Immediate specializations and dimension functions

Let `X` be a topological space and write `x ⤳ y` for `y ∈ closure {x}` (`Specializes`). A
non-trivial specialization `x ⤳ y`, `x ≠ y`, is *immediate* when no point lies strictly between
`x` and `y`; a map `δ : X → ℤ` is a *dimension function* when it drops strictly along every
non-trivial specialization and drops by exactly one along every immediate specialization.

## Main results

* `TopologicalSpace.isImmediateSpecialization_iff`: a specialization is immediate exactly when it
  is non-trivial and admits no intermediate point.
* `TopologicalSpace.exists_dimensionFunction_iff`: a function `δ : X → ℤ` underlies a
  `TopologicalSpace.DimensionFunction` exactly when it is strictly decreasing along non-trivial
  specializations and drops by exactly one along immediate specializations.

## References

* [Stacks Project, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9)
-/

@[expose] public section

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- A specialization is immediate exactly when it is non-trivial and admits no intermediate
point: every `z` with `x ⤳ z ⤳ y` is one of the two endpoints. -/
@[stacks 02I9]
theorem isImmediateSpecialization_iff (x y : X) :
    IsImmediateSpecialization x y ↔
      x ⤳ y ∧ x ≠ y ∧ ∀ z : X, x ⤳ z → z ⤳ y → z = x ∨ z = y :=
  Iff.rfl

/-- A function `δ : X → ℤ` is the underlying function of a dimension function exactly when it
is strictly decreasing along non-trivial specializations and drops by exactly one along
immediate specializations. -/
@[stacks 02I9]
theorem exists_dimensionFunction_iff (δ : X → ℤ) :
    (∃ d : DimensionFunction X, ∀ x, d x = δ x) ↔
      (∀ x y : X, x ⤳ y → x ≠ y → δ y < δ x) ∧
        (∀ x y : X, IsImmediateSpecialization x y → δ x = δ y + 1) := by
  refine ⟨fun ⟨d, hd⟩ => ⟨fun x y hxy hne => ?_, fun x y himm => ?_⟩,
    fun ⟨h₁, h₂⟩ => ⟨⟨δ, fun _ _ => h₁ _ _, fun _ _ => h₂ _ _⟩, fun _ => rfl⟩⟩ <;>
    rw [← hd x, ← hd y]
  · exact d.strictAnti_specializes hxy hne
  · exact d.step_immediate himm

end TopologicalSpace
