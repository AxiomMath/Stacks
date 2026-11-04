module

public import StacksFrontier.RingTheory.Cech.Substrate

/-!
# Subsets of a fixed size and strictly increasing tuples

A Čech cochain of degree `p` for a covering indexed by `Fin r` can be indexed either by the
`(p + 1)`-element subsets of `Fin r` or by the strictly increasing tuples
`Fin (p + 1) → Fin r`. The two indexings describe the same cochains, and the two shapes of the
Čech differential — the signed sum over the elements of a subset used by `Cech.cechSign`, and
the alternating sum over the positions of a tuple used by the ordered Čech complex — agree under
that identification.

This file supplies the three facts that make them agree: the bijection itself, the value of the
Čech sign at the `j`-th smallest element of a subset, and the compatibility of deleting an
element with omitting a position.

## Main definitions

* `Cech.orderedIndexEquiv`: the `(p + 1)`-element subsets of `Fin r` are the strictly increasing
  tuples `Fin (p + 1) → Fin r`, by sorting.

## Main results

* `Cech.card_filter_lt_orderEmbOfFin`: exactly `j` elements of a subset lie below its `j`-th
  smallest element.
* `Cech.cechSign_orderEmbOfFin`: **the Čech sign at the `j`-th smallest element of a subset is
  `(-1) ^ j`**, so the two shapes of the Čech differential carry the same signs.
* `Cech.orderEmbOfFin_erase`: **deleting the `j`-th smallest element of a subset and re-sorting
  omits the `j`-th position of the sorted tuple**, so the two shapes of the Čech differential
  have the same terms.

## Implementation notes

The sorting map is Mathlib's `Finset.orderEmbOfFin`, and all three proofs are applications of
its characterization `Finset.orderEmbOfFin_unique`: a strictly increasing tuple with values in a
subset of the right size *is* the sorting map of that subset. In particular no induction on the
subset appears.

`Cech.orderedIndexEquiv` is stated between subtypes rather than as an equivalence of the two
cochain groups, because the cochain groups are dependent products over these index types and the
comparison of the summands is a separate matter — the terms of a Čech complex at a tuple and at
the subset it enumerates are sections over opens that are equal but not syntactically so.

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public section

open Finset

namespace Cech

variable {r : ℕ}

/-- Exactly `j` elements of a subset lie strictly below its `j`-th smallest element. -/
public theorem card_filter_lt_orderEmbOfFin (S : Finset (Fin r)) {p : ℕ} (h : S.card = p + 1)
    (j : Fin (p + 1)) :
    (S.filter (· < S.orderEmbOfFin h j)).card = (j : ℕ) := by
  classical
  have himg : S.filter (· < S.orderEmbOfFin h j)
      = Finset.image (S.orderEmbOfFin h) (Finset.Iio j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    refine ⟨fun hx => ?_, ?_⟩
    · have hr : x ∈ Set.range (S.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin S h]
        exact hx.1
      obtain ⟨k, rfl⟩ := hr
      exact ⟨k, (S.orderEmbOfFin h).lt_iff_lt.1 hx.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨S.orderEmbOfFin_mem h k, (S.orderEmbOfFin h).strictMono hk⟩
  rw [himg, Finset.card_image_of_injective _ (S.orderEmbOfFin h).injective, Fin.card_Iio]

/-- **The Čech sign at the `j`-th smallest element of a subset is `(-1) ^ j`.** This is why the
signed sum over the elements of an index set and the alternating sum over the positions of a
strictly increasing tuple are the same differential. -/
public theorem cechSign_orderEmbOfFin (S : Finset (Fin r)) {p : ℕ} (h : S.card = p + 1)
    (j : Fin (p + 1)) :
    cechSign S (S.orderEmbOfFin h j) = (-1 : ℤ) ^ (j : ℕ) := by
  rw [cechSign, card_filter_lt_orderEmbOfFin S h j]

/-- **Deleting the `j`-th smallest element of a subset and re-sorting omits the `j`-th position
of the sorted tuple.** This is why the two shapes of the Čech differential have the same terms:
the face of an index set obtained by deleting an element is the face of the corresponding tuple
obtained by omitting the corresponding position. -/
public theorem orderEmbOfFin_erase (S : Finset (Fin r)) {p : ℕ} (h : S.card = p + 1)
    (j : Fin (p + 1)) (h' : (S.erase (S.orderEmbOfFin h j)).card = p) :
    ⇑((S.erase (S.orderEmbOfFin h j)).orderEmbOfFin h')
      = (S.orderEmbOfFin h) ∘ j.succAbove :=
  (Finset.orderEmbOfFin_unique h'
    (fun k => Finset.mem_erase.2
      ⟨fun hcon => Fin.succAbove_ne j k ((S.orderEmbOfFin h).injective hcon),
        S.orderEmbOfFin_mem h _⟩)
    ((S.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove j))).symm

/-- **The `(p + 1)`-element subsets of `Fin r` are the strictly increasing tuples
`Fin (p + 1) → Fin r`**, a subset going to the tuple that enumerates it in increasing order and
a tuple going to its range. -/
public noncomputable def orderedIndexEquiv {p : ℕ} :
    {S : Finset (Fin r) // S.card = p + 1} ≃
      {i : Fin (p + 1) → Fin r // StrictMono i} where
  toFun S := ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩
  invFun i := ⟨Finset.image i.1 Finset.univ, by
    rw [Finset.card_image_of_injective _ i.2.injective, Finset.card_univ, Fintype.card_fin]⟩
  left_inv S := Subtype.ext (Finset.coe_injective (by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]))
  right_inv i := Subtype.ext (funext fun x =>
    congrFun (Finset.orderEmbOfFin_unique
      (s := Finset.image i.1 Finset.univ) (k := p + 1)
      (by rw [Finset.card_image_of_injective _ i.2.injective, Finset.card_univ,
        Fintype.card_fin])
      (f := i.1)
      (fun y => Finset.mem_image.2 ⟨y, Finset.mem_univ y, rfl⟩) i.2).symm x)

end Cech

end
