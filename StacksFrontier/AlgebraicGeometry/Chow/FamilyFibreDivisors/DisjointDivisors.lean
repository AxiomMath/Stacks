module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections

/-!
# The two divisors of a family over the projective line are disjoint

Let `f : X ⟶ S` and let `W ⊆ X ×_S ℙ¹_S` be a closed subscheme. The zero divisor and the
infinity divisor of `W` are cut out by the images of the zero and of the infinity section, and
those images are disjoint. Hence `W₀` and `W_∞` are closed subschemes of `W` with disjoint
supports; in particular, a nonempty `W` cannot be swallowed by both sections at once, so at
most one of the two nondegeneracy hypotheses of Stacks Tag 02S4 can fail.

The same two images also compare the divisor on `W` with the fibre on `X`: the support of the
zero divisor and the support of the zero fibre have the same image in `X ×_S ℙ¹_S`, namely the
part of `W` lying on the zero section. This is the topological half of the assertion that `W₀`,
a divisor on `W`, may be regarded as a closed subscheme of `X`.

## Main results

* `Stacks.Chow.disjoint_support_zeroDivisor_infinityDivisor`: the two divisors of `W` have
  disjoint supports.
* `Stacks.Chow.isEmpty_subscheme_of_subset_range_both` and
  `Stacks.Chow.not_subset_range_infinitySection_of_subset_range_zeroSection`: a closed
  subscheme contained in the image of both sections is empty, so for a nonempty `W` the two
  degenerate cases excluded by Tag 02S4 are mutually exclusive.
* `Stacks.Chow.image_support_zeroDivisor_eq_image_support_zeroFiber` and
  `Stacks.Chow.image_support_infinityDivisor_eq_image_support_infinityFiber`: the divisor on
  `W` and the fibre on `X` have the same image in `X ×_S ℙ¹_S`.
* `Stacks.Chow.subset_range_zeroSection_iff_support_subset` and
  `Stacks.Chow.subset_range_infinitySection_iff_support_subset`: the nondegeneracy hypothesis
  of Tag 02S4 read on the support of `W` rather than on the range of its closed immersion.

## Implementation notes

Everything reduces to the two support computations of
`StacksFrontier/AlgebraicGeometry/Chow/FamilyFibreDivisors.lean` and
`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles.lean`, which present both supports as
preimages of the range of a section — of `W.subschemeι` for the divisor, of the section itself
for the fibre. Disjointness is then disjointness of preimages, and the image computations are
`Set.image_preimage_eq_inter_range` together with
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}} (f : X ⟶ S) (W : (projectiveLineProduct f).IdealSheafData)

/-- The zero divisor and the infinity divisor of a closed subscheme of `X ×_S ℙ¹_S` have
disjoint supports. -/
theorem disjoint_support_zeroDivisor_infinityDivisor :
    Disjoint ((zeroDivisor f W).support : Set W.subscheme)
      ((infinityDivisor f W).support : Set W.subscheme) := by
  rw [coe_support_zeroDivisor, coe_support_infinityDivisor]
  exact (disjoint_range_zeroSection_infinitySection f).preimage _

/-- A closed subscheme of `X ×_S ℙ¹_S` contained in the image of the zero section and in the
image of the infinity section is empty. -/
theorem isEmpty_subscheme_of_subset_range_both
    (h₀ : Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    IsEmpty W.subscheme :=
  ⟨fun w => Set.disjoint_left.mp (disjoint_range_zeroSection_infinitySection f)
    (h₀ ⟨w, rfl⟩) (hInf ⟨w, rfl⟩)⟩

/-- For a nonempty closed subscheme of `X ×_S ℙ¹_S` the two degenerate cases excluded by Stacks
Tag 02S4 are mutually exclusive: being contained in the image of the zero section forbids being
contained in the image of the infinity section. -/
theorem not_subset_range_infinitySection_of_subset_range_zeroSection [Nonempty W.subscheme]
    (h₀ : Set.range W.subschemeι ⊆ Set.range (zeroSection f)) :
    ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f) := fun hInf =>
  (isEmpty_subscheme_of_subset_range_both f W h₀ hInf).elim' (Classical.arbitrary _)

/-- The image in `X ×_S ℙ¹_S` of the support of the zero fibre is the part of the subscheme
lying on the zero section. -/
theorem image_support_zeroFiber :
    zeroSection f '' ((zeroFiber f W).support : Set X) =
      (W.support : Set (projectiveLineProduct f)) ∩ Set.range (zeroSection f) := by
  rw [coe_support_zeroFiber, Set.image_preimage_eq_inter_range]

/-- The image in `X ×_S ℙ¹_S` of the support of the infinity fibre is the part of the subscheme
lying on the infinity section. -/
theorem image_support_infinityFiber :
    infinitySection f '' ((infinityFiber f W).support : Set X) =
      (W.support : Set (projectiveLineProduct f)) ∩ Set.range (infinitySection f) := by
  rw [coe_support_infinityFiber, Set.image_preimage_eq_inter_range]

/-- The image in `X ×_S ℙ¹_S` of the support of the zero divisor is the part of the subscheme
lying on the zero section. -/
theorem image_support_zeroDivisor :
    W.subschemeι '' ((zeroDivisor f W).support : Set W.subscheme) =
      (W.support : Set (projectiveLineProduct f)) ∩ Set.range (zeroSection f) := by
  rw [coe_support_zeroDivisor, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι, Set.inter_comm]

/-- The image in `X ×_S ℙ¹_S` of the support of the infinity divisor is the part of the
subscheme lying on the infinity section. -/
theorem image_support_infinityDivisor :
    W.subschemeι '' ((infinityDivisor f W).support : Set W.subscheme) =
      (W.support : Set (projectiveLineProduct f)) ∩ Set.range (infinitySection f) := by
  rw [coe_support_infinityDivisor, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι, Set.inter_comm]

/-- The zero divisor of `W`, a closed subscheme of `W`, and the zero fibre of `W`, a closed
subscheme of `X`, have the same image in `X ×_S ℙ¹_S`. -/
theorem image_support_zeroDivisor_eq_image_support_zeroFiber :
    W.subschemeι '' ((zeroDivisor f W).support : Set W.subscheme) =
      zeroSection f '' ((zeroFiber f W).support : Set X) := by
  rw [image_support_zeroDivisor, image_support_zeroFiber]

/-- The infinity divisor of `W`, a closed subscheme of `W`, and the infinity fibre of `W`, a
closed subscheme of `X`, have the same image in `X ×_S ℙ¹_S`. -/
theorem image_support_infinityDivisor_eq_image_support_infinityFiber :
    W.subschemeι '' ((infinityDivisor f W).support : Set W.subscheme) =
      infinitySection f '' ((infinityFiber f W).support : Set X) := by
  rw [image_support_infinityDivisor, image_support_infinityFiber]

/-- Being contained in the image of the zero section is a condition on the support of the
closed subscheme. -/
theorem subset_range_zeroSection_iff_support_subset :
    Set.range W.subschemeι ⊆ Set.range (zeroSection f) ↔
      (W.support : Set (projectiveLineProduct f)) ⊆ Set.range (zeroSection f) := by
  rw [Scheme.IdealSheafData.range_subschemeι]

/-- Being contained in the image of the infinity section is a condition on the support of the
closed subscheme. -/
theorem subset_range_infinitySection_iff_support_subset :
    Set.range W.subschemeι ⊆ Set.range (infinitySection f) ↔
      (W.support : Set (projectiveLineProduct f)) ⊆ Set.range (infinitySection f) := by
  rw [Scheme.IdealSheafData.range_subschemeι]

end Stacks.Chow

end
