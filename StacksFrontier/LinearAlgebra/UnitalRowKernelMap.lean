module

public import StacksFrontier.LinearAlgebra.UnitalRowKernel

/-!
# Recognising the kernel of a unital coordinate row as the image of a linear map

Let `B` be a commutative ring, `ι` a finite index type, `x : ι → B` a family with `x i = 1`, and
`α : P →ₗ[B] (ι → B)` a linear map carrying a family `v` indexed by `{j // j ≠ i}` onto the
generators `e_j - x_j e_i` of the kernel of contraction with `x`. Then the image of `α` contains
that kernel, and if moreover the `v j` span `P` then `α` is injective.

## Main results

* `Stacks.LinearAlgebra.exists_apply_eq_of_unitalRow_eq_zero`: every vector annihilated by the
  row is in the image of `α`.
* `Stacks.LinearAlgebra.injective_of_span_eq_top`: if the `v j` span `P` then `α` is injective.
-/

@[expose] public section

namespace Stacks.LinearAlgebra

variable {B : Type*} [CommRing B] {ι : Type*} [DecidableEq ι]
  {i : ι} {x : ι → B} {P : Type*} [AddCommGroup P] [Module B P]

/-- If `α` sends each `v j` to `e_j - x_j e_i`, then every vector annihilated by the row `x` is in
the image of `α`. -/
theorem exists_apply_eq_of_unitalRow_eq_zero [Fintype ι] (hx : x i = 1) (α : P →ₗ[B] (ι → B))
    (v : {j : ι // j ≠ i} → P) (hv : ∀ j, α (v j) = kernelGen x i j.1)
    {g : ι → B} (hg : unitalRow x g = 0) :
    ∃ p, α p = g := by
  refine ⟨∑ j : {j : ι // j ≠ i}, g j.1 • v j, ?_⟩
  simp only [map_sum, map_smul, hv]
  rw [← kernelLift_apply]
  exact (eq_kernelLift_of_unitalRow_eq_zero hx hg).symm

/-- If `α` sends each `v j` to `e_j - x_j e_i` and the `v j` span `P`, then `α` is injective. -/
theorem injective_of_span_eq_top [Finite ι] (hx : x i = 1) (α : P →ₗ[B] (ι → B))
    (v : {j : ι // j ≠ i} → P) (hv : ∀ j, α (v j) = kernelGen x i j.1)
    (hspan : Submodule.span B (Set.range v) = ⊤) :
    Function.Injective α := by
  let : Fintype ι := Fintype.ofFinite ι
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun p hp => ?_
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp
    (hspan ▸ Submodule.mem_top : p ∈ Submodule.span B (Set.range v))
  have h0 : ∑ j : {j : ι // j ≠ i}, c j • kernelBasis hx j = 0 :=
    Submodule.injective_subtype _ (by simpa [map_sum, hv] using hp)
  simp [Fintype.linearIndependent_iff.mp (kernelBasis hx).linearIndependent c h0]

end Stacks.LinearAlgebra

end
