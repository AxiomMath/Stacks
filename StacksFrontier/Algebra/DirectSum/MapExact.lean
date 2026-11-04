module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# A direct sum of exact pairs of additive maps is exact

`DirectSum.map` applies a family of additive maps to a direct sum coordinatewise. Mathlib records
that it is injective exactly when the given family is injective in every coordinate
(`DirectSum.map_injective`) and surjective exactly when the family is
(`DirectSum.map_surjective`). This file adds the remaining third of short exactness: a direct sum
of exact pairs is an exact pair.

## Main results

* `DirectSum.exact_map`: **a direct sum of exact pairs of additive maps is an exact pair.**

## Implementation notes

The vanishing of the composite is coordinatewise, by `DirectSum.map_apply` and `DFinsupp.ext`.
The content is the other half, where a preimage has to be produced *with finite support*. It is
obtained by choosing, in each coordinate, a preimage *function* that sends `0` to `0` and applying
`DFinsupp.mapRange` to it: that keeps the support of the preimage inside the support of the
element, so no `Finset` bookkeeping appears. This is the argument of Mathlib's
`DFinsupp.mapRange_surjective`, with the preimage function defined only on the kernel and
extended by zero.

Nothing here is specific to a grading: the index type is arbitrary with decidable equality.
-/

@[expose] public section

universe u v

namespace DirectSum

variable {ι : Type u} [DecidableEq ι] {β₁ β₂ β₃ : ι → Type v}
  [∀ i, AddCommGroup (β₁ i)] [∀ i, AddCommGroup (β₂ i)] [∀ i, AddCommGroup (β₃ i)]

omit [DecidableEq ι] in
/-- **A direct sum of exact pairs is an exact pair.** -/
theorem exact_map (a : ∀ i, β₁ i →+ β₂ i) (b : ∀ i, β₂ i →+ β₃ i)
    (h : ∀ i, Function.Exact (a i) (b i)) : Function.Exact (map a) (map b) := by
  classical
  choose! u hu using fun (i : ι) (y : β₂ i) (hy : b i y = 0) => (h i y).1 hy
  refine fun w => ⟨fun hw => ?_, ?_⟩
  · have hker : ∀ i, b i (w i) = 0 := fun i => by
      rw [← map_apply b i w, hw, DFinsupp.zero_apply]
    refine ⟨DFinsupp.mapRange (fun i y => if y = 0 then 0 else u i y)
      (fun i => if_pos rfl) w, DFinsupp.ext fun i => ?_⟩
    rw [map_apply, DFinsupp.mapRange_apply]
    by_cases hi : w i = 0
    · rw [if_pos hi, map_zero, hi]
    · rw [if_neg hi]
      exact hu i (w i) (hker i)
  · rintro ⟨z, rfl⟩
    refine DFinsupp.ext fun i => ?_
    rw [map_apply, map_apply, DFinsupp.zero_apply]
    exact (h i).apply_apply_eq_zero (z i)

end DirectSum

end
