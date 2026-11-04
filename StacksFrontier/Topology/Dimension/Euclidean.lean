module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# The Krull dimension of Euclidean space is zero (Stacks 0056)

In a Hausdorff space an irreducible subset is a subsingleton, so no two irreducible closed
subsets are strictly ordered: the poset `TopologicalSpace.IrreducibleCloseds X` is an
antichain. If moreover `X` is nonempty then that poset is nonempty, so every chain has length
`0` and the supremum defining `topologicalKrullDim` is exactly `0` — not merely `≤ 0`, which
is all that Mathlib's `topologicalKrullDim_zero_of_discreteTopology` gives.

Euclidean space `ℝ^n` is Hausdorff and nonempty, so `dim ℝ^n = 0`, which is Stacks 0056.
Note that the topological Krull dimension is unrelated to the dimension of `ℝ^n` as a real
vector space or as a manifold.
-/

@[expose] public section

open TopologicalSpace

/-- In a Hausdorff space two irreducible closed subsets are never strictly ordered: the larger
one is a subsingleton, contradicting the strict inclusion. -/
private lemma TopologicalSpace.IrreducibleCloseds.not_lt_of_t2Space
    (X : Type*) [TopologicalSpace X] [T2Space X] (Z Z' : IrreducibleCloseds X) : ¬ Z < Z' := by
  intro hlt
  have hsub : (Z' : Set X).Subsingleton := Z'.isIrreducible'.isPreirreducible.subsingleton
  obtain ⟨x, hx⟩ := Z.isIrreducible'.nonempty
  exact hlt.not_ge fun y hy => by rw [hsub hy (hlt.le hx)]; exact hx

/-- In a nonempty Hausdorff space the irreducible closed subsets form a nonempty antichain,
hence the topological Krull dimension is `0`. -/
theorem topologicalKrullDim_eq_zero_of_t2Space (X : Type*) [TopologicalSpace X] [T2Space X]
    [Nonempty X] : topologicalKrullDim X = 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨{x}, isIrreducible_singleton, isClosed_singleton⟩⟩
  refine le_antisymm (iSup_le fun p => ?_) Order.krullDim_nonneg
  suffices hlen : p.length = 0 by simp [hlen]
  by_contra hne
  exact TopologicalSpace.IrreducibleCloseds.not_lt_of_t2Space X _ _
    (p.step ⟨0, Nat.pos_of_ne_zero hne⟩)

/-- **Stacks 0056.** The Krull dimension of the Euclidean space `ℝ^n` is `0`. -/
@[stacks 0056]
theorem topologicalKrullDim_euclideanSpace_eq_zero (n : ℕ) :
    topologicalKrullDim (EuclideanSpace ℝ (Fin n)) = 0 :=
  topologicalKrullDim_eq_zero_of_t2Space _
