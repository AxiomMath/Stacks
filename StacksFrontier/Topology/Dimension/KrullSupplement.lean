module

public import StacksFrontier.Topology.Dimension.Krull
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Topology.Dimension.Krull

/-!
# Additions to `Krull`

Further declarations supplementing the module above, kept in their own module.
-/

@[expose] public section

open TopologicalSpace

variable (X : Type*) [TopologicalSpace X]

section Nonneg

variable {T : Type*} [TopologicalSpace T]

/-- **The Krull dimension of a nonempty space is at least `0`.** The closure of a point is an
irreducible closed subset, so the poset of irreducible closed subsets -- whose `Order.krullDim`
the dimension is -- is nonempty. The nonemptiness is needed rather than incidental: an empty
space has dimension `⊥`, by `topologicalKrullDim_eq_bot_iff_isEmpty`.

The unfaithfulness scan flags this statement under its `Nonempty(...)`-weakening pattern. That is
a false positive, and the two reasons are worth recording here so the adjudication is not redone:
`[Nonempty T]` is an instance hypothesis on the space, not a `Nonempty (...)` wrapper around the
conclusion -- the conclusion is the inequality `0 ≤ topologicalKrullDim T`, which is not vacuous --
and the hypothesis cannot be dropped, since without it the statement is false for the empty space
by the `topologicalKrullDim_eq_bot_iff_isEmpty` just cited. The scan's pattern matches the token
`Nonempty` anywhere in a statement, including in an instance binder. -/
theorem topologicalKrullDim_nonneg [Nonempty T] : (0 : WithBot ℕ∞) ≤ topologicalKrullDim T :=
  have : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {Classical.arbitrary T}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  Order.krullDim_nonneg

end Nonneg

section NeBot

variable {X : Type*} [TopologicalSpace X]

end NeBot

section Discrete

variable {X : Type*} [TopologicalSpace X]

end Discrete

section Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

end Homeomorph

section Embedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

end Embedding

section Subspace

variable {X : Type*} [TopologicalSpace X]

end Subspace

section FiniteValue

end FiniteValue


