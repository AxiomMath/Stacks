module

public import StacksFrontier.LinearAlgebra.SubspaceUnionCodim

/-!
# A tower of injections between finite-dimensional spaces is eventually a tower of isomorphisms

Let `V 0, V 1, V 2, …` be finite-dimensional vector spaces over a field `k` joined by injective
linear maps `V (j + 1) → V j`. The dimensions are then non-increasing, so they are eventually
constant, and an injective map between spaces of the same finite dimension is bijective. Hence
from some index on every map of the tower is an isomorphism.

## Main results

* `Stacks.LinearAlgebra.exists_forall_bijective_of_injective_tower`: the tower is eventually a
  tower of bijections.

## Implementation notes

Eventual constancy of the dimensions is
`Stacks.LinearAlgebra.exists_forall_eq_of_antitone`; what is added here is that an injective map
between finite-dimensional spaces of equal dimension is surjective, which is read off the
dimension of its range.

This is the step of [Stacks, Tag 0FD8] which turns "multiplication by a section is injective on
`H¹(X, ℱ ⊗ ℒ^{⊗ m})` for `m ≪ 0`" into "it is an isomorphism there", which is what makes the
annihilator of the multiplication independent of `m`.

## References

* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
-/

@[expose] public section

universe u v

namespace Stacks.LinearAlgebra

variable (k : Type u) [Field k] (V : ℕ → Type v) [∀ j, AddCommGroup (V j)]
  [∀ j, Module k (V j)] [∀ j, FiniteDimensional k (V j)]

/-- **A tower of injections between finite-dimensional spaces is eventually a tower of
bijections.** -/
public theorem exists_forall_bijective_of_injective_tower (φ : ∀ j : ℕ, V (j + 1) →ₗ[k] V j)
    (hφ : ∀ j, Function.Injective (φ j)) :
    ∃ J : ℕ, ∀ j, J ≤ j → Function.Bijective (φ j) := by
  obtain ⟨J, N, hJ⟩ := exists_forall_eq_of_antitone (fun j => Module.finrank k (V j))
    fun j => (φ j).finrank_le_finrank_of_injective (hφ j)
  refine ⟨J, fun j hj => ⟨hφ j, ?_⟩⟩
  have hdim : Module.finrank k (V (j + 1)) = Module.finrank k (V j) :=
    (hJ (j + 1) (hj.trans (Nat.le_succ j))).trans (hJ j hj).symm
  refine LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq ?_)
  rw [LinearMap.finrank_range_of_inj (hφ j)]
  exact hdim

end Stacks.LinearAlgebra

end
