module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A criterion for a semilinear map to be a base change

Let `k ⟶ k'` be a field extension, `V` a finite-dimensional `k`-vector space and `V'` a
`k'`-vector space of the same finite dimension, and let `β : V → V'` be additive and semilinear
over `k ⟶ k'`. Suppose that whenever `∑ cᵢ β(vᵢ) = 0` with `cᵢ ∈ k'`, also `∑ ℓ(cᵢ) vᵢ = 0` for
every `k`-linear form `ℓ` on `k'`. Then `β` is injective and its image spans `V'` over `k'`;
that is, `V'` is the base change of `V`.

The hypothesis is what a trace map `V' → V` for each form `ℓ` provides.

## Main results

* `Stacks.LinearAlgebra.injective_and_span_eq_top_of_forall_dual`: the criterion.
-/

@[expose] public section

namespace Stacks.LinearAlgebra

open Module

variable {k k' : Type*} [Field k] [Field k'] [Algebra k k']
  {V V' : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup V'] [Module k' V'] [FiniteDimensional k' V']

/-- **A semilinear map compatible with all linear forms on `k'` is a base change.** -/
theorem injective_and_span_eq_top_of_forall_dual (hdim : finrank k' V' = finrank k V)
    (β : V →+ V') (hβ : ∀ (c : k) (v : V), β (c • v) = algebraMap k k' c • β v)
    (htr : ∀ (c : Fin (finrank k V) → k') (v : Fin (finrank k V) → V),
      ∑ i, c i • β (v i) = 0 → ∀ ℓ : k' →ₗ[k] k, ∑ i, ℓ (c i) • v i = 0) :
    Function.Injective β ∧ Submodule.span k' (Set.range β) = ⊤ := by
  let b := Module.finBasis k V
  have hli : LinearIndependent k' (fun i => β (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    exact (forall_dual_apply_eq_zero_iff k (c i)).mp fun ℓ =>
      Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => ℓ (c j)) (htr c b hc ℓ) i
  have hexp : ∀ v : V, β v = ∑ i, algebraMap k k' (b.repr v i) • β (b i) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hβ _ _
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hexp v] at hv
    refine b.ext_elem fun i => ?_
    simpa using (FaithfulSMul.algebraMap_injective k k').eq_iff.mp
      ((Fintype.linearIndependent_iff.mp hli _ hv i).trans (map_zero _).symm)
  · refine eq_top_iff.mpr ((hli.span_eq_top_of_card_eq_finrank' (by simp [hdim])).ge.trans ?_)
    exact Submodule.span_mono (Set.range_comp_subset_range _ _)

end Stacks.LinearAlgebra

end
