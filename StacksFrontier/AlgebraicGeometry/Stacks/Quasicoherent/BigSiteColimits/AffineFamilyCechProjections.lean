module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The Čech projections of a covering family

Descent along a covering *family* `{g i : Y i ⟶ T}` runs through the first two differentials of
the Čech complex of that family, whose terms are the products of the sections over the members,
over the double overlaps `Pb i j = Y i ×_T Y j` and over the triple overlaps
`Pb₃ i j k = Y i ×_T Pb j k`.  The second differential is written with three projections of a
triple overlap onto the double overlaps, subject to the three commutations which say that the two
descriptions of each of its three projections onto the members agree.

Only one of the three projections onto the double overlaps is part of the data of an iterated
fibre product: the triple overlap is built as a fibre product of the first member with the double
overlap of the last two, so the projection onto `Pb j k` is one of its two legs while the two
projections onto `Pb i j` and onto `Pb i k` have to be produced.  This file produces them, from the
universal property of the two double overlaps concerned, together with the identifications of
their composites with the two projections of those double overlaps.

This is the family analogue of `CategoryTheory.IsPullback.exists_cechProjections`, which is the
same statement for the one-element family, where all three legs land in the single double
self-product.  At a family the three legs land in three *different* double overlaps, so the
one-element statement does not specialise to it and the mixed indices have to be carried through;
the proof is otherwise the same two applications of a universal property.

## Main results

* `CategoryTheory.IsPullback.exists_familyCechProjections`: **the two remaining projections of a
  triple overlap of a covering family onto double overlaps**, with the identifications of their
  composites with the projections of those double overlaps.

## Implementation notes

The two composites with the first projections are identified with the given leg `q i j k` onto the
first member rather than with each other.  That is strictly more information, and both forms are
used: the equality of the two composites is the first of the three commutations a Čech differential
asks for, while the identification with `q i j k` is what makes the ring map a triple overlap
induces on global functions factor through each of the two double overlaps.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0238](https://stacks.math.columbia.edu/tag/0238)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

universe v u

namespace CategoryTheory.IsPullback

/-- **The two remaining projections of a triple overlap of a covering family onto double
overlaps.**

Let `{g i : Y i ⟶ T}` be a family, let `Pb i j` be a fibre product of `g i` and `g j` with
projections `pr₁ i j` and `pr₂ i j`, and let `Pb₃ i j k` be a fibre product of `g i` with the
composite `pr₁ j k ≫ g j`, with legs `q i j k` onto `Y i` and `t₂₃ i j k` onto `Pb j k`.  Then
there are projections `t₁₂ i j k` onto `Pb i j` and `t₁₃ i j k` onto `Pb i k` whose composites with
the first projections are `q i j k` and whose composites with the second projections are the two
legs of `t₂₃ i j k`.

Together these say that the three projections of `Pb₃ i j k` onto the members `Y i`, `Y j` and
`Y k` each have two descriptions which agree: the equality
`t₁₂ i j k ≫ pr₁ i j = t₁₃ i j k ≫ pr₁ i k` of the first two conclusions, and the third and fourth
conclusions themselves.  Those three equalities are the commutations
`PresheafOfModules.exists_family_datum_of_baseChange` consumes, while the identifications with
`q i j k` are what identify the ring maps a triple overlap of affine objects induces. -/
theorem exists_familyCechProjections {C : Type u} [Category.{v} C] {T : C} {ι : Type*}
    {Y : ι → C} {g : ∀ i, Y i ⟶ T} {Pb : ι → ι → C}
    {pr₁ : ∀ i j, Pb i j ⟶ Y i} {pr₂ : ∀ i j, Pb i j ⟶ Y j}
    (hpb : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j))
    {Pb₃ : ι → ι → ι → C} {q : ∀ i j k, Pb₃ i j k ⟶ Y i}
    {t₂₃ : ∀ i j k, Pb₃ i j k ⟶ Pb j k}
    (hpb₃ : ∀ i j k, IsPullback (q i j k) (t₂₃ i j k) (g i) (pr₁ j k ≫ g j)) :
    ∃ (t₁₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i j) (t₁₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i k),
      (∀ i j k, t₁₂ i j k ≫ pr₁ i j = q i j k) ∧
      (∀ i j k, t₁₃ i j k ≫ pr₁ i k = q i j k) ∧
      (∀ i j k, t₁₂ i j k ≫ pr₂ i j = t₂₃ i j k ≫ pr₁ j k) ∧
      (∀ i j k, t₁₃ i j k ≫ pr₂ i k = t₂₃ i j k ≫ pr₂ j k) := by
  have key : ∀ i j k m (h : Pb j k ⟶ Y m), pr₁ j k ≫ g j = h ≫ g m →
      ∃ t : Pb₃ i j k ⟶ Pb i m, t ≫ pr₁ i m = q i j k ∧ t ≫ pr₂ i m = t₂₃ i j k ≫ h :=
    fun i j k m h hw =>
      ⟨(hpb i m).lift (q i j k) (t₂₃ i j k ≫ h)
          (by rw [Category.assoc, ← hw]; exact (hpb₃ i j k).w),
        (hpb i m).lift_fst .., (hpb i m).lift_snd ..⟩
  choose t₁₂ h₁ h₃ using fun i j k => key i j k j (pr₁ j k) rfl
  choose t₁₃ h₂ h₄ using fun i j k => key i j k k (pr₂ j k) (hpb j k).w
  exact ⟨t₁₂, t₁₃, h₁, h₂, h₃, h₄⟩

end CategoryTheory.IsPullback

end
