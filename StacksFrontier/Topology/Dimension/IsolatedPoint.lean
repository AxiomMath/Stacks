module

public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Separation.IsolatedPoint

/-!
# The Krull dimension of a space at an isolated point

An isolated point has an open neighbourhood with one element, so the infimum defining
`topologicalKrullDimAt` at that point is computed on a one-point space and is zero.

## Main results

* `topologicalKrullDimAt_eq_zero_of_isIsolatedPoint`: the Krull dimension of a topological
  space at an isolated point is `0`.
-/

@[expose] public section

open TopologicalSpace

/-- The Krull dimension of a topological space at an isolated point is `0`.

The singleton spanned by the point is an open neighbourhood whose Krull dimension is `0`,
because it carries the discrete topology, and this bounds the infimum of
`topologicalKrullDimAt` from above; the infimum is at least `0` because every open
neighbourhood of the point contains the irreducible closed subset `closure {x}`. -/
theorem topologicalKrullDimAt_eq_zero_of_isIsolatedPoint {X : Type*} [TopologicalSpace X]
    (x : X) (hx : IsIsolatedPoint x) : topologicalKrullDimAt X x = 0 := by
  obtain ⟨⟨U, hxU, hU, hdim⟩, hle⟩ := topologicalKrullDimAt_isLeast X x
  refine le_antisymm ?_ ?_
  · have : Subsingleton ({x} : Set X) :=
      ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    exact (hle ⟨{x}, rfl, hx, rfl⟩).trans
      (topologicalKrullDim_zero_of_discreteTopology ({x} : Set X))
  · let : Nonempty (IrreducibleCloseds U) :=
      ⟨⟨closure {⟨x, hxU⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact hdim ▸ Order.krullDim_nonneg

end
