module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of grading shifts

Let `S` be a commutative `R`-algebra graded by `𝒜 : ℤ → Submodule R S`. The *shift* `S(a)` of
`S` by an integer `a` is `S` again as an `S`-module, graded so that its degree-`i` piece is
`𝒜 (i + a)`. Multiplication in `S` identifies `S(a) ⊗_S S(b)` with `S(a + b)`, and this file
records that identification one graded piece at a time.

## Main results

* `GradedAlgebra.map_lid_span_shift_tmul`: the image under multiplication of the degree-`n`
  piece of `S(a) ⊗_S S(b)` is the degree-`n` piece of `S(a + b)`, namely `𝒜 (n + (a + b))`.

## Implementation notes

The underlying module of every shift is `S` itself, so no shift datatype is introduced: a
shift is recorded only through its grading, and the degree-`n` piece of the tensor product is
written out as the `R`-span of the homogeneous pure tensors `x ⊗ₜ y` with `x ∈ 𝒜 (i + a)`,
`y ∈ 𝒜 (j + b)` and `i + j = n`. The canonical multiplication map is Mathlib's
`TensorProduct.lid S S`, which sends `x ⊗ₜ y` to `x * y`; it is restricted to `R`-linear maps
so that both sides are `R`-submodules of `S`.

Stating the identification as an equality of images — rather than as injectivity plus
surjectivity of a graded map — records both halves at once: the inclusion `≤` is multiplicative
closedness of the grading, and `≥` follows by writing a homogeneous element `x` of degree
`n + (a + b)` as the image of `1 ⊗ₜ x`.

Specializing to a weighted polynomial grading with `a = 1`, `b = 2` gives the identification
`S(1) ⊗_S S(2) = S(3)` used in the analysis of twists on `Proj`.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public noncomputable section

namespace GradedAlgebra

universe u v

/-- Multiplication identifies each piece of `S(a) ⊗ₛ S(b)` with the corresponding
piece of `S(a + b)` for a graded commutative algebra. -/
public theorem map_lid_span_shift_tmul {R : Type u} {S : Type v}
    [CommSemiring R] [CommRing S] [Algebra R S]
    (𝒜 : ℤ → Submodule R S) [GradedAlgebra 𝒜] (a b n : ℤ) :
    Submodule.map ((TensorProduct.lid S S).toLinearMap.restrictScalars R)
      (Submodule.span R
        {t : TensorProduct S S S |
          ∃ i j : ℤ, i + j = n ∧
            ∃ x y : S, x ∈ 𝒜 (i + a) ∧
              y ∈ 𝒜 (j + b) ∧ t = TensorProduct.tmul S x y}) =
      𝒜 (n + (a + b)) := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr ?_)) ?_
  · rintro t ⟨i, j, hij, x, y, hx, hy, rfl⟩; change x * y ∈ 𝒜 (n + (a + b))
    simpa only [show (i + a) + (j + b) = n + (a + b) by omega] using SetLike.mul_mem_graded hx hy
  · intro x hx; refine Submodule.mem_map.mpr ⟨TensorProduct.tmul S 1 x, ?_, by simp⟩
    exact Submodule.subset_span ⟨-a, n + a, by omega, 1, x,
      by simpa using (SetLike.one_mem_graded 𝒜), by simpa [add_assoc] using hx, rfl⟩

end GradedAlgebra

end
