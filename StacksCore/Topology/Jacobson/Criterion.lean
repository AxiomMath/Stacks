module

public import Mathlib.Topology.JacobsonSpace

/-!
# A criterion for a topological space to be Jacobson

## Main results

* `jacobson_check_irreducible_closed`: if for every point `x` the closed points contained in
  `closure {x}` are dense in `closure {x}`, then the space is Jacobson.

## References

* [Stacks Project, Tag 005V](https://stacks.math.columbia.edu/tag/005V)
-/

@[expose] public section

/-- **Stacks 005V**. Let `X` be a topological space and `X₀` its set of closed
points. If for every point `x` the intersection `X₀ ∩ closure {x}` is dense in
`closure {x}` (equivalently, `closure (closedPoints X ∩ closure {x}) = closure {x}`),
then `X` is a Jacobson space. -/
@[stacks 005V]
theorem jacobson_check_irreducible_closed
    {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, closure (closedPoints X ∩ closure ({x} : Set X)) = closure ({x} : Set X)) :
    JacobsonSpace X := by
  refine ⟨fun {Z} hZ => subset_antisymm
    (hZ.closure_subset_iff.mpr Set.inter_subset_left) fun x hxZ => ?_⟩
  have hclmono : closure ({x} : Set X) ⊆ closure (Z ∩ closedPoints X) := by
    rw [← h x]
    exact closure_mono fun _ ⟨hy1, hy2⟩ =>
      ⟨hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxZ) hy2, hy1⟩
  exact hclmono (subset_closure rfl)
