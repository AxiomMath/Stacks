module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The structure maps of a direct sum of two objects

Let `b` be a binary bicone over `X` and `Y` in a preadditive category: an object `b.pt` with
maps `i = b.inl`, `j = b.inr`, `p = b.fst`, `q = b.snd` satisfying `p ∘ i = id`, `q ∘ j = id`,
`p ∘ j = 0` and `q ∘ i = 0`. Then `b` is a direct sum (a bilimit) exactly when
`i ∘ p + j ∘ q = id`, and for a direct sum the injections are determined by the projections
through these four relations, and the projections by the injections.

## Main results

* `CategoryTheory.Limits.BinaryBicone.nonempty_isBilimit_iff_total_and_unique`: the binary
  bicone `b` is a bilimit if and only if `i ∘ p + j ∘ q = id`, and if it is a bilimit then
  `i, j` are the only maps satisfying the four relations with `p, q`, and `p, q` the only maps
  satisfying them with `i, j`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C]

/-- In a preadditive category, a binary bicone `b` over `X` and `Y` (maps `i = b.inl`,
`j = b.inr`, `p = b.fst`, `q = b.snd` with `p ∘ i = id`, `q ∘ j = id`, `p ∘ j = 0`, `q ∘ i = 0`)
is a direct sum of `X` and `Y` if and only if `i ∘ p + j ∘ q = id`. Moreover, if `b` is a direct
sum, then given the projections `p, q` the injections are the only maps `i', j'` with
`p ∘ i' = id`, `q ∘ j' = id`, `p ∘ j' = 0`, `q ∘ i' = 0`, and given the injections `i, j` the
projections are the only maps `p', q'` with `p' ∘ i = id`, `q' ∘ j = id`, `p' ∘ j = 0`,
`q' ∘ i = 0`. -/
@[stacks 0103 "all three parts: uniqueness of `i, j` given `p, q` together with \
  `i ∘ p + j ∘ q = id`, uniqueness of `p, q` given `i, j`, and the recognition criterion \
  (a bicone with `i ∘ p + j ∘ q = id` is a direct sum); the data of the recognition criterion \
  is Mathlib's `isBinaryBilimitOfTotal`"]
theorem BinaryBicone.nonempty_isBilimit_iff_total_and_unique {X Y : C} (b : BinaryBicone X Y) :
    (Nonempty b.IsBilimit ↔ b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) ∧
    (Nonempty b.IsBilimit →
      (∀ (i : X ⟶ b.pt) (j : Y ⟶ b.pt), i ≫ b.fst = 𝟙 X → j ≫ b.snd = 𝟙 Y → j ≫ b.fst = 0 →
        i ≫ b.snd = 0 → i = b.inl ∧ j = b.inr) ∧
      (∀ (p : b.pt ⟶ X) (q : b.pt ⟶ Y), b.inl ≫ p = 𝟙 X → b.inr ≫ q = 𝟙 Y → b.inr ≫ p = 0 →
        b.inl ≫ q = 0 → p = b.fst ∧ q = b.snd)) := by
  refine ⟨⟨fun ⟨hb⟩ => IsBilimit.binary_total hb, fun h => ⟨isBinaryBilimitOfTotal b h⟩⟩,
    fun ⟨hb⟩ => ⟨fun i j hi hj hjp hiq => ⟨?_, ?_⟩, fun p q hp hq hjp hiq => ⟨?_, ?_⟩⟩⟩
  · exact BinaryFan.IsLimit.hom_ext hb.isLimit (by simpa using hi) (by simpa using hiq)
  · exact BinaryFan.IsLimit.hom_ext hb.isLimit (by simpa using hjp) (by simpa using hj)
  · exact BinaryCofan.IsColimit.hom_ext hb.isColimit (by simpa using hp) (by simpa using hjp)
  · exact BinaryCofan.IsColimit.hom_ext hb.isColimit (by simpa using hiq) (by simpa using hq)

end CategoryTheory.Limits
