module

public import StacksFrontier.RingTheory.Cech.Reindex
public import StacksFrontier.RingTheory.Localization.IteratedAway

/-!
# The Čech complex of a concatenated family of elements

Let `R` be a commutative ring, let `f : Fin r → R` and `g : Fin m → R` be two finite families of
elements of `R` and let `M` be an `R`-module. This file compares the extended alternating Čech
complex of the concatenated family `Fin.append f g : Fin (r + m) → R` with the Čech complexes of
the two pieces, summand by summand.

An index set `u : Finset (Fin (r + m))` for the concatenated family splits into the part coming
from the first block and the part coming from the second,

`leftPart u = {i : Fin r // castAdd i ∈ u}`,  `rightPart u = {j : Fin m // natAdd j ∈ u}`,

and this splitting is a bijection onto pairs of index sets, with cardinalities adding. Under it
the localizing element factors,
`∏_{x ∈ u} (f ++ g) x = (∏_{i ∈ leftPart u} f i) · (∏_{j ∈ rightPart u} g j)`, so by
`LocalizedModule.iteratedAwayEquiv` the summand of `C^•(f ++ g; M)` indexed by `u` is the summand
of `C^•(f; C^•(g; M))` indexed by `(leftPart u, rightPart u)`:

`M_{∏_u (f ++ g)} ≅ (M_{∏_{rightPart u} g})_{∏_{leftPart u} f}`.

## The sign convention

The Čech differential of the concatenated family inserts a new index `x ∉ u` with the sign
`Cech.cechSign u x = (-1)^{#{y ∈ u : y < x}}`. The two blocks behave differently, and this is the
Koszul sign of the total complex of a double complex, computed rather than imposed:

* inserting an index `castAdd i` of the **first** block picks up `Cech.cechSign (leftPart u) i` —
  no extra factor, because every element of `u` below `castAdd i` lies in the first block
  (`Cech.cechSign_castAdd`);
* inserting an index `natAdd j` of the **second** block picks up
  `(-1)^{#(leftPart u)} · Cech.cechSign (rightPart u) j` — the whole of the first block lies below
  `natAdd j`, so the count of elements of `u` below it is `#(leftPart u)` plus the count inside the
  second block (`Cech.cechSign_natAdd`).

So on the summand indexed by `u`, with `p = #(leftPart u)`, the differential of
`C^•(f ++ g; M)` is `d_f + (-1)^p d_g`: the first block supplies the horizontal differential and
the second the vertical one, weighted by `(-1)^p`. This is exactly the differential of the total
complex of the double complex `(p, q) ↦ C^p(f; C^q(g; M))`.

## Main definitions

* `Cech.leftPart`, `Cech.rightPart` — the two halves of an index set of the concatenated family.
* `Cech.joinParts` — the index set assembled from a pair of index sets.
* `Cech.PairIdx`, `Cech.idxAppendEquiv` — the index type of a term of the total complex of
  `(p, q) ↦ C^p(f; C^q(g; M))`, and its identification with the index type of the concatenated
  family.
* `Cech.appendModEquiv` — the identification of a single summand,
  `M_{∏_u (f ++ g)} ≅ (M_{∏_{rightPart u} g})_{∏_{leftPart u} f}`.
* `Cech.pairModEquiv` — the same identification with the pair of index sets as the primary datum.
* `Cech.localizedCechι` — a transition map of the second family, localized at a product over an
  index set of the first.
* `Cech.appendTermEquiv` — the degreewise identification of `C^n(f ++ g; M)` with the direct sum,
  over the degree-`n` index sets, of the summands of the iterated construction.

## Main results

* `Cech.joinParts_leftPart_rightPart`, `Cech.leftPart_joinParts`, `Cech.rightPart_joinParts` —
  splitting an index set is a bijection onto pairs of index sets.
* `Cech.card_leftPart_add_card_rightPart`, `Cech.card_joinParts` — cardinalities add.
* `Cech.prod_append_eq` — the localizing element factors.
* `Cech.cechSub_append` — the localizing submonoid of the concatenated family, in factored form.
* `Cech.cechSign_castAdd`, `Cech.cechSign_natAdd` — **the sign convention**, as described above.
* `Cech.appendModEquiv_mk_one`, `Cech.pairModEquiv_mk_one` — the summand identifications on the
  canonical generator.
* `Cech.pairModEquiv_cechι_left`, `Cech.pairModEquiv_cechι_right` — **naturality of the summand
  identification for the two blocks of transition maps**: the transition maps of the concatenated
  family become the transition maps of the first family in one block and, in the other, the
  transition maps of the second family localized at a product over an index set of the first.
* `Cech.isUnit_algebraMap_pairMod` — both factors of the localizing element act invertibly on an
  iterated localization at larger index sets, which is what makes the two naturality statements
  checkable on the canonical generator.

## Implementation notes

`Cech.joinParts` is built with `Finset.image` rather than `Finset.map`: `Fin.castAddEmb` is
implemented through `Fin.castLEEmb`, so its coercion does not reduce to `Fin.castAdd`, and every
membership rewrite then has to fight the embedding. With `Finset.image` the membership lemmas
`Finset.mem_image` speak about `Fin.castAdd` directly, at the cost of using
`Finset.card_image_of_injective` and `Finset.prod_image` in place of their `Finset.map`
counterparts.

The two blocks of indices are kept apart by `Cech.castAdd_ne_natAdd`, the only arithmetic input:
an index of the first block has value `< r` and an index of the second has value `≥ r`.

## References

* [Stacks Project, Tag 0G6F](https://stacks.math.columbia.edu/tag/0G6F), Section 15.30, the
  extended alternating Čech complex.
* [Stacks Project, Tag 0ECP](https://stacks.math.columbia.edu/tag/0ECP), the subadditivity of
  cohomological dimension, for which this is the combinatorial input.
-/

@[expose] public section

open Finset

namespace Cech

universe u v

variable {r m : ℕ}

/-! ### The two blocks of indices are disjoint -/

/-- An index of the first block never equals an index of the second: the first has value `< r`
and the second has value `≥ r`. -/
theorem castAdd_ne_natAdd (i : Fin r) (j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd r j := by
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at hval
  have := i.isLt
  omega

/-- The images of the two blocks in `Fin (r + m)` are disjoint. -/
theorem disjoint_image_castAdd_natAdd (s : Finset (Fin r)) (t : Finset (Fin m)) :
    Disjoint (s.image (Fin.castAdd m)) (t.image (Fin.natAdd r)) := by
  simp only [Finset.disjoint_left, Finset.mem_image]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, hbe⟩
  exact castAdd_ne_natAdd a b hbe.symm

/-! ### Splitting an index set -/

/-- The part of an index set of the concatenated family coming from the first block. -/
def leftPart (u : Finset (Fin (r + m))) : Finset (Fin r) :=
  Finset.univ.filter fun i => Fin.castAdd m i ∈ u

/-- The part of an index set of the concatenated family coming from the second block. -/
def rightPart (u : Finset (Fin (r + m))) : Finset (Fin m) :=
  Finset.univ.filter fun j => Fin.natAdd r j ∈ u

/-- Membership in the first part is membership of the corresponding first-block index. -/
@[simp] theorem mem_leftPart {u : Finset (Fin (r + m))} {i : Fin r} :
    i ∈ leftPart u ↔ Fin.castAdd m i ∈ u := by
  simp [leftPart]

/-- Membership in the second part is membership of the corresponding second-block index. -/
@[simp] theorem mem_rightPart {u : Finset (Fin (r + m))} {j : Fin m} :
    j ∈ rightPart u ↔ Fin.natAdd r j ∈ u := by
  simp [rightPart]

/-- The index set of the concatenated family assembled from an index set for each block. -/
def joinParts (s : Finset (Fin r)) (t : Finset (Fin m)) : Finset (Fin (r + m)) :=
  s.image (Fin.castAdd m) ∪ t.image (Fin.natAdd r)

/-- An index of the first block lies in an assembled index set exactly when it lies in the first
of the two index sets. -/
@[simp] theorem mem_joinParts_castAdd (s : Finset (Fin r)) (t : Finset (Fin m)) (i : Fin r) :
    Fin.castAdd m i ∈ joinParts s t ↔ i ∈ s := by
  simp only [joinParts, Finset.mem_union, Finset.mem_image]
  refine ⟨?_, fun h => Or.inl ⟨i, h, rfl⟩⟩
  rintro (⟨a, ha, hae⟩ | ⟨a, ha, hae⟩)
  · exact Fin.castAdd_injective _ _ hae ▸ ha
  · exact absurd hae.symm (castAdd_ne_natAdd i a)

/-- An index of the second block lies in an assembled index set exactly when it lies in the second
of the two index sets. -/
@[simp] theorem mem_joinParts_natAdd (s : Finset (Fin r)) (t : Finset (Fin m)) (j : Fin m) :
    Fin.natAdd r j ∈ joinParts s t ↔ j ∈ t := by
  simp only [joinParts, Finset.mem_union, Finset.mem_image]
  refine ⟨?_, fun h => Or.inr ⟨j, h, rfl⟩⟩
  rintro (⟨a, ha, hae⟩ | ⟨a, ha, hae⟩)
  · exact absurd hae (castAdd_ne_natAdd a j)
  · exact Fin.natAdd_injective _ _ hae ▸ ha

/-- The first part of an assembled index set is the first of the two index sets. -/
@[simp] theorem leftPart_joinParts (s : Finset (Fin r)) (t : Finset (Fin m)) :
    leftPart (joinParts s t) = s := by
  ext i
  rw [mem_leftPart, mem_joinParts_castAdd]

/-- The second part of an assembled index set is the second of the two index sets. -/
@[simp] theorem rightPart_joinParts (s : Finset (Fin r)) (t : Finset (Fin m)) :
    rightPart (joinParts s t) = t := by
  ext j
  rw [mem_rightPart, mem_joinParts_natAdd]

/-- **Splitting an index set is a bijection.** Every index of the concatenated family belongs to
exactly one of the two blocks, so an index set is recovered from its two parts. -/
@[simp] theorem joinParts_leftPart_rightPart (u : Finset (Fin (r + m))) :
    joinParts (leftPart u) (rightPart u) = u := by
  ext x
  induction x using Fin.addCases with
  | left i => rw [mem_joinParts_castAdd, mem_leftPart]
  | right j => rw [mem_joinParts_natAdd, mem_rightPart]

/-- The splitting is injective on pairs of index sets. -/
theorem joinParts_injective {s s' : Finset (Fin r)} {t t' : Finset (Fin m)}
    (h : joinParts s t = joinParts s' t') : s = s' ∧ t = t' :=
  ⟨by rw [← leftPart_joinParts s t, h, leftPart_joinParts],
   by rw [← rightPart_joinParts s t, h, rightPart_joinParts]⟩

/-! ### Cardinalities -/

/-- The cardinality of an assembled index set is the sum of the two cardinalities. -/
theorem card_joinParts (s : Finset (Fin r)) (t : Finset (Fin m)) :
    (joinParts s t).card = s.card + t.card := by
  rw [joinParts, Finset.card_union_of_disjoint (disjoint_image_castAdd_natAdd s t),
    Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
    Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)]

/-- The cardinalities of the two parts of an index set add up to its cardinality: this is the
degree bookkeeping `n = p + q` of the total complex. -/
theorem card_leftPart_add_card_rightPart (u : Finset (Fin (r + m))) :
    (leftPart u).card + (rightPart u).card = u.card := by
  rw [← card_joinParts, joinParts_leftPart_rightPart]

/-! ### Inserting a new index -/

/-- Inserting an index of the first block. -/
theorem joinParts_insert_left (s : Finset (Fin r)) (t : Finset (Fin m)) (i : Fin r) :
    joinParts (insert i s) t = insert (Fin.castAdd m i) (joinParts s t) := by
  ext x
  induction x using Fin.addCases with
  | left a =>
    rw [mem_joinParts_castAdd, Finset.mem_insert, Finset.mem_insert, mem_joinParts_castAdd]
    exact or_congr_left ⟨fun h => by rw [h], fun h => Fin.castAdd_injective _ _ h⟩
  | right b =>
    rw [mem_joinParts_natAdd, Finset.mem_insert, mem_joinParts_natAdd]
    exact (or_iff_right (castAdd_ne_natAdd i b).symm).symm

/-- Inserting an index of the second block. -/
theorem joinParts_insert_right (s : Finset (Fin r)) (t : Finset (Fin m)) (j : Fin m) :
    joinParts s (insert j t) = insert (Fin.natAdd r j) (joinParts s t) := by
  ext x
  induction x using Fin.addCases with
  | left a =>
    rw [mem_joinParts_castAdd, Finset.mem_insert, mem_joinParts_castAdd]
    exact (or_iff_right (castAdd_ne_natAdd a j)).symm
  | right b =>
    rw [mem_joinParts_natAdd, Finset.mem_insert, Finset.mem_insert, mem_joinParts_natAdd]
    exact or_congr_left ⟨fun h => by rw [h], fun h => Fin.natAdd_injective _ _ h⟩

/-- Inserting an index of the first block changes only the first part. -/
@[simp] theorem leftPart_insert_castAdd (u : Finset (Fin (r + m))) (i : Fin r) :
    leftPart (insert (Fin.castAdd m i) u) = insert i (leftPart u) := by
  rw [← joinParts_leftPart_rightPart u, ← joinParts_insert_left, leftPart_joinParts,
    leftPart_joinParts]

/-- Inserting an index of the first block leaves the second part unchanged. -/
@[simp] theorem rightPart_insert_castAdd (u : Finset (Fin (r + m))) (i : Fin r) :
    rightPart (insert (Fin.castAdd m i) u) = rightPart u := by
  rw [← joinParts_leftPart_rightPart u, ← joinParts_insert_left, rightPart_joinParts,
    rightPart_joinParts]

/-- Inserting an index of the second block changes only the second part. -/
@[simp] theorem rightPart_insert_natAdd (u : Finset (Fin (r + m))) (j : Fin m) :
    rightPart (insert (Fin.natAdd r j) u) = insert j (rightPart u) := by
  rw [← joinParts_leftPart_rightPart u, ← joinParts_insert_right, rightPart_joinParts,
    rightPart_joinParts]

/-- Inserting an index of the second block leaves the first part unchanged. -/
@[simp] theorem leftPart_insert_natAdd (u : Finset (Fin (r + m))) (j : Fin m) :
    leftPart (insert (Fin.natAdd r j) u) = leftPart u := by
  rw [← joinParts_leftPart_rightPart u, ← joinParts_insert_right, leftPart_joinParts,
    leftPart_joinParts]

/-! ### Erasing an index -/

/-- Erasing an index of the first block changes only the first part. -/
@[simp] theorem leftPart_erase_castAdd (u : Finset (Fin (r + m))) (i : Fin r) :
    leftPart (u.erase (Fin.castAdd m i)) = (leftPart u).erase i := by
  ext a
  rw [mem_leftPart, Finset.mem_erase, Finset.mem_erase, mem_leftPart]
  exact and_congr_left' (not_congr ⟨fun h => Fin.castAdd_injective _ _ h, fun h => by rw [h]⟩)

/-- Erasing an index of the first block leaves the second part unchanged. -/
@[simp] theorem rightPart_erase_castAdd (u : Finset (Fin (r + m))) (i : Fin r) :
    rightPart (u.erase (Fin.castAdd m i)) = rightPart u := by
  ext b
  rw [mem_rightPart, Finset.mem_erase, mem_rightPart]
  exact and_iff_right (castAdd_ne_natAdd i b).symm

/-- Erasing an index of the second block changes only the second part. -/
@[simp] theorem rightPart_erase_natAdd (u : Finset (Fin (r + m))) (j : Fin m) :
    rightPart (u.erase (Fin.natAdd r j)) = (rightPart u).erase j := by
  ext b
  rw [mem_rightPart, Finset.mem_erase, Finset.mem_erase, mem_rightPart]
  exact and_congr_left' (not_congr ⟨fun h => Fin.natAdd_injective _ _ h, fun h => by rw [h]⟩)

/-- Erasing an index of the second block leaves the first part unchanged. -/
@[simp] theorem leftPart_erase_natAdd (u : Finset (Fin (r + m))) (j : Fin m) :
    leftPart (u.erase (Fin.natAdd r j)) = leftPart u := by
  ext a
  rw [mem_leftPart, Finset.mem_erase, mem_leftPart]
  exact and_iff_right (castAdd_ne_natAdd a j)

/-! ### The index types -/

/-- The index type of the degree-`n` term of the total complex of the double complex
`(p, q) ↦ C^p(f; C^q(g; M))`: a pair of index sets whose cardinalities add up to `n`. -/
abbrev PairIdx (r m n : ℕ) :=
  { w : Finset (Fin r) × Finset (Fin m) // w.1.card + w.2.card = n }

/-- **The degree-`n` index sets of the concatenated family are the pairs of index sets of total
cardinality `n`.** This is the reindexing datum of the degreewise comparison between
`C^n(f ++ g; M)` and the degree-`n` term of the total complex of
`(p, q) ↦ C^p(f; C^q(g; M))`. -/
def idxAppendEquiv (n : ℕ) : ExtendedAlternatingCech.Idx (r + m) n ≃ PairIdx r m n where
  toFun u := ⟨(leftPart u.1, rightPart u.1),
    (card_leftPart_add_card_rightPart u.1).trans u.2⟩
  invFun w := ⟨joinParts w.1.1 w.1.2, (card_joinParts w.1.1 w.1.2).trans w.2⟩
  left_inv u := Subtype.ext (joinParts_leftPart_rightPart u.1)
  right_inv w := Subtype.ext (Prod.ext (leftPart_joinParts w.1.1 w.1.2)
    (rightPart_joinParts w.1.1 w.1.2))

/-- The first component of the reindexing is the first part. -/
@[simp] theorem idxAppendEquiv_apply_fst (n : ℕ) (u : ExtendedAlternatingCech.Idx (r + m) n) :
    (idxAppendEquiv n u).1.1 = leftPart u.1 := rfl

/-- The second component of the reindexing is the second part. -/
@[simp] theorem idxAppendEquiv_apply_snd (n : ℕ) (u : ExtendedAlternatingCech.Idx (r + m) n) :
    (idxAppendEquiv n u).1.2 = rightPart u.1 := rfl

/-- The inverse of the reindexing assembles the pair of index sets. -/
@[simp] theorem idxAppendEquiv_symm_apply (n : ℕ) (w : PairIdx r m n) :
    ((idxAppendEquiv n).symm w).1 = joinParts w.1.1 w.1.2 := rfl

/-! ### The localizing element factors -/

variable {R : Type u} [CommRing R]

/-- The product over an assembled index set of the concatenated family factors as the product over
the first part times the product over the second. -/
theorem prod_joinParts (f : Fin r → R) (g : Fin m → R) (s : Finset (Fin r))
    (t : Finset (Fin m)) :
    ∏ x ∈ joinParts s t, Fin.append f g x = (∏ i ∈ s, f i) * ∏ j ∈ t, g j := by
  rw [joinParts, Finset.prod_union (disjoint_image_castAdd_natAdd s t),
    Finset.prod_image (fun a _ b _ h => Fin.castAdd_injective _ _ h),
    Finset.prod_image (fun a _ b _ h => Fin.natAdd_injective _ _ h)]
  simp only [Fin.append_left, Fin.append_right]

/-- **The localizing element of the concatenated family factors.** -/
theorem prod_append_eq (f : Fin r → R) (g : Fin m → R) (u : Finset (Fin (r + m))) :
    ∏ x ∈ u, Fin.append f g x =
      (∏ i ∈ leftPart u, f i) * ∏ j ∈ rightPart u, g j := by
  rw [← joinParts_leftPart_rightPart u, prod_joinParts, leftPart_joinParts, rightPart_joinParts]

/-- The localizing submonoid of the concatenated family, in factored form. -/
theorem cechSub_append (f : Fin r → R) (g : Fin m → R) (u : Finset (Fin (r + m))) :
    cechSub (Fin.append f g) u =
      Submonoid.powers ((∏ i ∈ leftPart u, f i) * ∏ j ∈ rightPart u, g j) := by
  rw [cechSub, prod_append_eq]

/-! ### The sign convention -/

/-- The elements of `u` below an index of the first block are exactly the first-block elements
below it. -/
theorem filter_lt_castAdd (u : Finset (Fin (r + m))) (i : Fin r) :
    u.filter (· < Fin.castAdd m i) = ((leftPart u).filter (· < i)).image (Fin.castAdd m) := by
  ext x
  induction x using Fin.addCases with
  | left a =>
    simp only [Finset.mem_filter, Finset.mem_image, mem_leftPart, Fin.lt_def, Fin.val_castAdd]
    refine ⟨fun h => ⟨a, ⟨h.1, h.2⟩, rfl⟩, ?_⟩
    rintro ⟨b, ⟨hb, hblt⟩, hbe⟩
    obtain rfl := Fin.castAdd_injective _ _ hbe
    exact ⟨hb, hblt⟩
  | right b =>
    simp only [Finset.mem_filter, Finset.mem_image, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    have hi := i.isLt
    refine ⟨fun h => absurd h.2 (by omega), ?_⟩
    rintro ⟨c, _, hce⟩
    exact absurd hce (castAdd_ne_natAdd c b)

/-- The elements of `u` below an index of the second block are the whole of the first part
together with the second-block elements below it. -/
theorem filter_lt_natAdd (u : Finset (Fin (r + m))) (j : Fin m) :
    u.filter (· < Fin.natAdd r j) =
      (leftPart u).image (Fin.castAdd m) ∪
        ((rightPart u).filter (· < j)).image (Fin.natAdd r) := by
  ext x
  induction x using Fin.addCases with
  | left a =>
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, mem_leftPart, Fin.lt_def,
      Fin.val_castAdd, Fin.val_natAdd]
    have ha := a.isLt
    refine ⟨fun h => Or.inl ⟨a, h.1, rfl⟩, ?_⟩
    rintro (⟨b, hb, hbe⟩ | ⟨c, _, hce⟩)
    · obtain rfl := Fin.castAdd_injective _ _ hbe
      exact ⟨hb, by omega⟩
    · exact absurd hce.symm (castAdd_ne_natAdd a c)
  | right b =>
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, mem_rightPart, Fin.lt_def,
      Fin.val_natAdd]
    refine ⟨fun h => Or.inr ⟨b, ⟨h.1, by omega⟩, rfl⟩, ?_⟩
    rintro (⟨c, _, hce⟩ | ⟨c, ⟨hc, hclt⟩, hce⟩)
    · exact absurd hce (castAdd_ne_natAdd c b)
    · obtain rfl := Fin.natAdd_injective _ _ hce
      exact ⟨hc, by omega⟩

/-- **Inserting an index of the first block costs no extra sign.** Every element of `u` below an
index of the first block lies in the first block, so the Čech sign of the concatenated family
agrees with the Čech sign of the first part. -/
theorem cechSign_castAdd (u : Finset (Fin (r + m))) (i : Fin r) :
    cechSign u (Fin.castAdd m i) = cechSign (leftPart u) i := by
  rw [cechSign, cechSign, filter_lt_castAdd,
    Finset.card_image_of_injective _ (Fin.castAdd_injective _ _)]

/-- **Inserting an index of the second block costs the Koszul sign.** The whole of the first part
lies below an index of the second block, so the Čech sign of the concatenated family is
`(-1)^{#(leftPart u)}` times the Čech sign of the second part. With `p = #(leftPart u)` this is the
sign `(-1)^p` in front of the vertical differential of a total complex. -/
theorem cechSign_natAdd (u : Finset (Fin (r + m))) (j : Fin m) :
    cechSign u (Fin.natAdd r j) =
      (-1) ^ (leftPart u).card * cechSign (rightPart u) j := by
  rw [cechSign, cechSign, filter_lt_natAdd,
    Finset.card_union_of_disjoint (disjoint_image_castAdd_natAdd _ _),
    Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
    Finset.card_image_of_injective _ (Fin.natAdd_injective _ _), pow_add]

/-! ### The summand identification -/

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Identifying a localization with an iterated one fixes the fraction `x/1`, whichever equality of
submonoids is used. -/
private theorem congr_trans_iteratedAwayEquiv_symm_mk_one {S : Submonoid R} (a b : R)
    (h : S = Submonoid.powers (a * b)) (x : M) :
    ((localizedCongr M h).trans (LocalizedModule.iteratedAwayEquiv M a b).symm)
        (LocalizedModule.mk x 1) = LocalizedModule.mk (LocalizedModule.mk x 1) 1 := by
  rw [LinearEquiv.trans_apply, localizedCongr_mk_one, LinearEquiv.symm_apply_eq,
    LocalizedModule.iteratedAwayEquiv_mk_mk]

/-- **A single summand of the Čech complex of a concatenated family.** The localization of `M` at
the product over an index set `u` of the concatenated family is the localization, at the product
over `leftPart u` of the first family, of the localization of `M` at the product over
`rightPart u` of the second family. In other words the summand of `C^•(f ++ g; M)` indexed by `u`
is the summand of `C^•(f; C^•(g; M))` indexed by the pair `(leftPart u, rightPart u)`. -/
noncomputable def appendModEquiv (f : Fin r → R) (g : Fin m → R) (u : Finset (Fin (r + m))) :
    cechMod (Fin.append f g) M u ≃ₗ[R]
      cechMod f (cechMod g M (rightPart u)) (leftPart u) :=
  (localizedCongr M (cechSub_append f g u)).trans
    (LocalizedModule.iteratedAwayEquiv M (∏ i ∈ leftPart u, f i)
      (∏ j ∈ rightPart u, g j)).symm

/-- The summand identification fixes the canonical generator: the fraction `m/1` of the
concatenated family goes to the fraction `(m/1)/1` of the iterated localization. -/
theorem appendModEquiv_mk_one (f : Fin r → R) (g : Fin m → R) (u : Finset (Fin (r + m)))
    (x : M) :
    appendModEquiv M f g u (LocalizedModule.mk x 1) =
      LocalizedModule.mk (LocalizedModule.mk x 1) 1 :=
  congr_trans_iteratedAwayEquiv_symm_mk_one M _ _ _ x

/-! ### The pair-indexed summand, and naturality of the identification -/

/-- Enlarging the first index set enlarges the assembled index set. -/
theorem joinParts_subset_left {s s' : Finset (Fin r)} (hs : s ⊆ s') (t : Finset (Fin m)) :
    joinParts s t ⊆ joinParts s' t :=
  Finset.union_subset_union_left (Finset.image_subset_image hs)

/-- Enlarging the second index set enlarges the assembled index set. -/
theorem joinParts_subset_right (s : Finset (Fin r)) {t t' : Finset (Fin m)} (ht : t ⊆ t') :
    joinParts s t ⊆ joinParts s t' :=
  Finset.union_subset_union_right (Finset.image_subset_image ht)

/-- **The summand identification, with the pair of index sets as the primary datum.** This is
`Cech.appendModEquiv` at `u = Cech.joinParts s t`, but stated so that the target is literally
`cechMod f (cechMod g M t) s`; in that form it needs no transport along
`Cech.leftPart_joinParts` and `Cech.rightPart_joinParts`, which is what makes the naturality
statements below type-check as written. -/
noncomputable def pairModEquiv (f : Fin r → R) (g : Fin m → R) (s : Finset (Fin r))
    (t : Finset (Fin m)) :
    cechMod (Fin.append f g) M (joinParts s t) ≃ₗ[R] cechMod f (cechMod g M t) s :=
  (localizedCongr M (congrArg Submonoid.powers (prod_joinParts f g s t))).trans
    (LocalizedModule.iteratedAwayEquiv M (∏ i ∈ s, f i) (∏ j ∈ t, g j)).symm

/-- The pair-indexed summand identification fixes the canonical generator. -/
@[simp] theorem pairModEquiv_mk_one (f : Fin r → R) (g : Fin m → R) (s : Finset (Fin r))
    (t : Finset (Fin m)) (x : M) :
    pairModEquiv M f g s t (LocalizedModule.mk x 1) =
      LocalizedModule.mk (LocalizedModule.mk x 1) 1 :=
  congr_trans_iteratedAwayEquiv_symm_mk_one M _ _ _ x

/-- Both factors of the localizing element of the concatenated family act invertibly on an
iterated localization at larger index sets: the first factor because it is inverted by the outer
localization, the second because it is inverted by the inner one and invertible scalars survive
the outer localization. -/
theorem isUnit_algebraMap_pairMod (f : Fin r → R) (g : Fin m → R)
    {s s' : Finset (Fin r)} (hs : s ⊆ s') {t t' : Finset (Fin m)} (ht : t ⊆ t') :
    IsUnit (algebraMap R (Module.End R (cechMod f (cechMod g M t') s'))
      ((∏ i ∈ s, f i) * ∏ j ∈ t, g j)) := by
  rw [map_mul]
  refine IsUnit.mul ?_ ?_
  · exact isUnit_algebraMap f (cechMod g M t') hs
      (LocalizedModule.mkLinearMap (cechSub f s') (cechMod g M t'))
      ⟨∏ i ∈ s, f i, Submonoid.mem_powers _⟩
  · exact LocalizedModule.isUnit_algebraMap_end_of_isUnit _
      (isUnit_algebraMap g M ht (LocalizedModule.mkLinearMap (cechSub g t') M)
        ⟨∏ j ∈ t, g j, Submonoid.mem_powers _⟩)

/-- Every element of the localizing submonoid of the concatenated family at `joinParts s t` acts
invertibly on an iterated localization at larger index sets. -/
theorem isUnit_algebraMap_pairMod_mem (f : Fin r → R) (g : Fin m → R)
    {s s' : Finset (Fin r)} (hs : s ⊆ s') {t t' : Finset (Fin m)} (ht : t ⊆ t')
    (z : cechSub (Fin.append f g) (joinParts s t)) :
    IsUnit (algebraMap R (Module.End R (cechMod f (cechMod g M t') s')) (z : R)) := by
  obtain ⟨k, hk⟩ := z.2
  have hz : (z : R) = ((∏ i ∈ s, f i) * ∏ j ∈ t, g j) ^ k := by
    rw [← hk, prod_joinParts]
  rw [hz, map_pow]
  exact (isUnit_algebraMap_pairMod M f g hs ht).pow k

/-- The transition map of the inner Čech complex, carried along the outer localization: the map
`(M_{∏_t g})_{∏_s f} → (M_{∏_{t'} g})_{∏_s f}` induced by `Cech.cechι g M ht`. This is the
vertical differential's constituent on a single summand. -/
noncomputable abbrev localizedCechι (f : Fin r → R) (g : Fin m → R) (s : Finset (Fin r))
    {t t' : Finset (Fin m)} (ht : t ⊆ t') :
    cechMod f (cechMod g M t) s →ₗ[R] cechMod f (cechMod g M t') s :=
  IsLocalizedModule.map (cechSub f s)
    (LocalizedModule.mkLinearMap (cechSub f s) (cechMod g M t))
    (LocalizedModule.mkLinearMap (cechSub f s) (cechMod g M t'))
    (cechι g M ht)

/-- `Cech.localizedCechι` fixes the canonical generator. -/
@[simp] theorem localizedCechι_mk_one (f : Fin r → R) (g : Fin m → R) (s : Finset (Fin r))
    {t t' : Finset (Fin m)} (ht : t ⊆ t') (x : M) :
    localizedCechι M f g s ht (LocalizedModule.mk (LocalizedModule.mk x 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk x 1) 1 := by
  rw [localizedCechι, IsLocalizedModule.map_LocalizedModules, cechι_mk_one]

/-- A map out of a summand of the concatenated family commutes with the summand identification
as soon as it does so on the canonical generator. -/
private theorem pairModEquiv_cechι_eq (f : Fin r → R) (g : Fin m → R) {s s' : Finset (Fin r)}
    (hs : s ⊆ s') {t t' : Finset (Fin m)} (ht : t ⊆ t') (hst : joinParts s t ⊆ joinParts s' t')
    (φ : cechMod f (cechMod g M t) s →ₗ[R] cechMod f (cechMod g M t') s')
    (hφ : ∀ x : M, φ (LocalizedModule.mk (LocalizedModule.mk x 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk x 1) 1)
    (x : cechMod (Fin.append f g) M (joinParts s t)) :
    pairModEquiv M f g s' t' (cechι (Fin.append f g) M hst x) = φ (pairModEquiv M f g s t x) := by
  have key : (pairModEquiv M f g s' t').toLinearMap.comp (cechι (Fin.append f g) M hst)
      = φ.comp (pairModEquiv M f g s t).toLinearMap := by
    refine IsLocalizedModule.ext (cechSub (Fin.append f g) (joinParts s t))
      (LocalizedModule.mkLinearMap (cechSub (Fin.append f g) (joinParts s t)) M)
      (fun z => isUnit_algebraMap_pairMod_mem M f g hs ht z)
      (LinearMap.ext fun y => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LocalizedModule.mkLinearMap_apply,
      cechι_mk_one, pairModEquiv_mk_one, hφ]
  exact LinearMap.congr_fun key x

/-- **Naturality in the first block.** Enlarging the first index set, the summand identification
turns the transition map of the concatenated family into the transition map of the Čech complex
of the first family, with coefficients in the summand `M_{∏_t g}` of the second. This is the
horizontal differential's constituent on a single summand. -/
theorem pairModEquiv_cechι_left (f : Fin r → R) (g : Fin m → R) {s s' : Finset (Fin r)}
    (hs : s ⊆ s') (t : Finset (Fin m)) (x : cechMod (Fin.append f g) M (joinParts s t)) :
    pairModEquiv M f g s' t
        (cechι (Fin.append f g) M (joinParts_subset_left hs t) x) =
      cechι f (cechMod g M t) hs (pairModEquiv M f g s t x) :=
  pairModEquiv_cechι_eq M f g hs (subset_refl t) _ _ (fun _ => cechι_mk_one ..) x

/-- **Naturality in the second block.** Enlarging the second index set, the summand identification
turns the transition map of the concatenated family into the transition map of the Čech complex of
the second family, localized at the product over the first index set. This is the vertical
differential's constituent on a single summand. -/
theorem pairModEquiv_cechι_right (f : Fin r → R) (g : Fin m → R) (s : Finset (Fin r))
    {t t' : Finset (Fin m)} (ht : t ⊆ t')
    (x : cechMod (Fin.append f g) M (joinParts s t)) :
    pairModEquiv M f g s t'
        (cechι (Fin.append f g) M (joinParts_subset_right s ht) x) =
      localizedCechι M f g s ht (pairModEquiv M f g s t x) :=
  pairModEquiv_cechι_eq M f g (subset_refl s) ht _ _ (fun _ => localizedCechι_mk_one ..) x

/-! ### The degreewise identification -/

/-- **The degree-`n` term of the Čech complex of a concatenated family.** Summand by summand it
is a term of the iterated Čech construction: the summand indexed by `u` is the localization, at
the product over `leftPart u` of the first family, of the summand of `C^•(g; M)` indexed by
`rightPart u`.

The index type is kept as the index type `ExtendedAlternatingCech.Idx (r + m) n` of the
concatenated family rather than being transported along `Cech.idxAppendEquiv` to pairs: the two
spellings of a summand agree only propositionally (`Cech.leftPart_joinParts` is proved by
`Finset.ext`, not by `rfl`), so the pair-indexed form needs an explicit transport, whereas in this
form every summand's type is the one the construction produces. -/
noncomputable def appendTermEquiv (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    cechTerm (Fin.append f g) M n ≃ₗ[R]
      DirectSum (ExtendedAlternatingCech.Idx (r + m) n)
        fun u => cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1) :=
  DirectSum.congrLinearEquiv fun u => appendModEquiv M f g u.1

/-- The degreewise identification acts summandwise. -/
@[simp] theorem appendTermEquiv_lof (f : Fin r → R) (g : Fin m → R) (n : ℕ)
    (u : ExtendedAlternatingCech.Idx (r + m) n) (z : cechMod (Fin.append f g) M u.1) :
    appendTermEquiv M f g n
        (DirectSum.lof R _ (fun v => cechMod (Fin.append f g) M v.1) u z) =
      DirectSum.lof R _
        (fun v => cechMod f (cechMod g M (rightPart v.1)) (leftPart v.1)) u
        (appendModEquiv M f g u.1 z) := by
  simp only [appendTermEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
    LinearEquiv.coe_coe]

/-- The degreewise identification on the canonical generator of a summand. -/
theorem appendTermEquiv_lof_mk_one (f : Fin r → R) (g : Fin m → R) (n : ℕ)
    (u : ExtendedAlternatingCech.Idx (r + m) n) (x : M) :
    appendTermEquiv M f g n
        (DirectSum.lof R _ (fun v => cechMod (Fin.append f g) M v.1) u
          (LocalizedModule.mk x 1)) =
      DirectSum.lof R _
        (fun v => cechMod f (cechMod g M (rightPart v.1)) (leftPart v.1)) u
        (LocalizedModule.mk (LocalizedModule.mk x 1) 1) := by
  rw [appendTermEquiv_lof, appendModEquiv_mk_one]

end Cech

end
