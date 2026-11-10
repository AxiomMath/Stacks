module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs

/-!
# Proper intersection and the linear structure of cycles

Two cycles intersect properly when every pair of their components does (Tag 0AZQ). This file
records how that condition interacts with the group structure of cycles: it passes to sums,
differences and multiples, and it can be checked one component at a time. It also writes a cycle
with finitely many components as the sum of the multiples of the prime cycles of those
components.

## Main results

* `AlgebraicGeometry.AlgebraicCycle.intersectProperly_of_forall_closure`: proper intersection
  read at the points carrying nonzero coefficients, and its converse
  `AlgebraicGeometry.AlgebraicCycle.IntersectProperly.of_ne_zero`.
* `AlgebraicGeometry.AlgebraicCycle.intersectProperly_sum_left` and its companions: proper
  intersection is preserved by finite sums, multiples and differences.
* `AlgebraicGeometry.AlgebraicCycle.intersectProperly_of_forall_single`: it suffices to meet the
  prime cycle of each component properly.
* `AlgebraicGeometry.AlgebraicCycle.eq_sum_zsmul_single`: `α = ∑ᵥ α(v) [closure {v}]`.

## References

* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public section

open TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace AlgebraicCycle

variable {X : Scheme.{u}}

/-- Proper intersection of two cycles, read at the points carrying nonzero coefficients. -/
theorem intersectProperly_of_forall_closure {α β : AlgebraicCycle X ℤ}
    (h : ∀ x y : X, α x ≠ 0 → β y ≠ 0 → AlgebraicGeometry.IntersectProperly
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    IntersectProperly α β := by
  intro W V hW hV
  have hW' : W = ⟨closure {W.isIrreducible.genericPoint}, isIrreducible_singleton.closure,
      isClosed_closure⟩ :=
    IrreducibleCloseds.ext (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).symm
  have hV' : V = ⟨closure {V.isIrreducible.genericPoint}, isIrreducible_singleton.closure,
      isClosed_closure⟩ :=
    IrreducibleCloseds.ext (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).symm
  rw [hW', hV']
  exact h _ _ hW hV

/-- The pointwise reading of proper intersection: the closures of two points carrying nonzero
coefficients intersect properly. -/
theorem IntersectProperly.of_ne_zero {α β : AlgebraicCycle X ℤ} (h : IntersectProperly α β)
    {x y : X} (hx : α x ≠ 0) (hy : β y ≠ 0) :
    AlgebraicGeometry.IntersectProperly
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
  have hgen : ∀ z : X, (isIrreducible_singleton (x := z)).closure.genericPoint = z := fun z =>
    (isGenericPoint_closure.eq
      ((isIrreducible_singleton (x := z)).closure.isGenericPoint_genericPoint
        isClosed_closure)).symm
  h _ _ (by rwa [hgen]) (by rwa [hgen])

/-- A finite sum of cycles each meeting `β` properly meets `β` properly. -/
theorem intersectProperly_sum_left {ι : Type*} (S : Finset ι) (A : ι → AlgebraicCycle X ℤ)
    {β : AlgebraicCycle X ℤ} (h : ∀ i ∈ S, IntersectProperly (A i) β) :
    IntersectProperly (∑ i ∈ S, A i) β := by
  intro W V hW hV
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply] at hW
  obtain ⟨i, hi, hAi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hW
  exact h i hi W V hAi hV

/-- A cycle meeting each of finitely many cycles properly meets their sum properly. -/
theorem intersectProperly_sum_right {ι : Type*} (S : Finset ι) (B : ι → AlgebraicCycle X ℤ)
    {α : AlgebraicCycle X ℤ} (h : ∀ i ∈ S, IntersectProperly α (B i)) :
    IntersectProperly α (∑ i ∈ S, B i) := by
  intro W V hW hV
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply] at hV
  obtain ⟨i, hi, hBi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
  exact h i hi W V hW hBi

/-- A multiple of a cycle meeting `β` properly meets `β` properly. -/
theorem intersectProperly_zsmul_left (c : ℤ) {α β : AlgebraicCycle X ℤ}
    (h : IntersectProperly α β) : IntersectProperly (c • α) β := by
  intro W V hW hV
  exact h W V (fun h0 => hW (by simp [h0])) hV

/-- A cycle meeting `β` properly meets every multiple of `β` properly. -/
theorem intersectProperly_zsmul_right (c : ℤ) {α β : AlgebraicCycle X ℤ}
    (h : IntersectProperly α β) : IntersectProperly α (c • β) := by
  intro W V hW hV
  exact h W V hW (fun h0 => hV (by simp [h0]))

/-- The sum of two cycles meeting `β` properly meets `β` properly. -/
theorem intersectProperly_add_left {α α' β : AlgebraicCycle X ℤ} (h : IntersectProperly α β)
    (h' : IntersectProperly α' β) : IntersectProperly (α + α') β := by
  intro W V hW hV
  by_cases hα : α W.isIrreducible.genericPoint = 0
  · refine h' W V (fun h0 => hW ?_) hV
    simp [hα, h0]
  · exact h W V hα hV

/-- The difference of two cycles meeting `β` properly meets `β` properly. -/
theorem intersectProperly_sub_left {α α' β : AlgebraicCycle X ℤ} (h : IntersectProperly α β)
    (h' : IntersectProperly α' β) : IntersectProperly (α - α') β := by
  intro W V hW hV
  by_cases hα : α W.isIrreducible.genericPoint = 0
  · refine h' W V (fun h0 => hW ?_) hV
    simp [hα, h0]
  · exact h W V hα hV

/-- A cycle meets `β` properly as soon as it meets the prime cycle of each component of `β`
properly. -/
theorem intersectProperly_of_forall_single [DecidableEq X] {α β : AlgebraicCycle X ℤ}
    (h : ∀ v, β v ≠ 0 → IntersectProperly α (Function.locallyFinsuppWithin.single v (1 : ℤ))) :
    IntersectProperly α β := by
  intro W V hW hV
  exact h _ hV W V hW (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_left rfl]; simp)

/-- **A cycle with finitely many components is the sum of the multiples of the prime cycles of
its components**: `α = ∑ᵥ α(v) [closure {v}]`. On a quasi-compact scheme the finiteness
hypothesis is automatic. -/
theorem eq_sum_zsmul_single [DecidableEq X] {α : AlgebraicCycle X ℤ}
    (hα : (Function.support α).Finite) :
    α = ∑ v ∈ hα.toFinset, α v • Function.locallyFinsuppWithin.single v (1 : ℤ) := by
  refine Function.locallyFinsuppWithin.ext fun z => ?_
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hz : z ∈ hα.toFinset
  · rw [ite_eq_left hz]
  · rw [ite_eq_right hz]
    exact Function.notMem_support.1 fun h => hz (hα.mem_toFinset.2 h)

end AlgebraicCycle

end AlgebraicGeometry

end
