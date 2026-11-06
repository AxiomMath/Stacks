module

public import Mathlib.SetTheory.Cardinal.Aleph
public import StacksFrontier.Order.CoherentFiniteToOne

/-!
# The countable ordinals as an index

The constructions of `StacksFrontier.Order.CoherentFiniteToOne` and everything built on them run
over an abstract index: a well-ordered type which is uncountable and all of whose proper initial
segments are countable. This file provides the instance, so that nothing downstream is
conditional on such a type existing.

The type is `Ordinal.ToType (ω_ 1)`, the countable ordinals, which lives in the same universe as
the rings of the construction rather than one above — that is why `Ordinal.ToType` is used and
not `Set.Iio (ω_ 1)`.

## Main definitions

* `Stacks.Coherent.OmegaOne`: the countable ordinals, as a type in `Type u`.

## Main results

* `Stacks.Coherent.instUncountableOmegaOne`: it is uncountable.
* `Stacks.Coherent.countable_Iio_omegaOne`: each of its proper initial segments is countable.
* `Stacks.Coherent.exists_index`: the abstract index of the construction is inhabited.

## Implementation notes

Both facts are the two directions of `Cardinal.lt_ord` at `ℵ₁`, whose `ord` is `ω_ 1`: the whole
type has cardinality `(ω_ 1).card = ℵ₁`, which is not countable, while an initial segment has
cardinality the cardinality of the ordinal it is the order type of, and that ordinal is below
`ω_ 1`.

The boundedness of countable subsets, which the gluing arguments also need, is *not* proved here:
`Stacks.Coherent.exists_gt_of_countable` derives it from these two facts, so the regularity of
`ℵ₁` never has to be invoked.
-/

@[expose] public noncomputable section

namespace Stacks.Coherent

open Cardinal Ordinal

universe u

/-- The countable ordinals, as a type in `Type u`. This is the index of the coherent sequence and
of the twisted system built from it. -/
abbrev OmegaOne := Ordinal.ToType (ω_ 1 : Ordinal.{u})

/-- The countable ordinals are `ℵ₁` in number. -/
theorem mk_omegaOne : #(OmegaOne.{u}) = ℵ₁ := by
  rw [Cardinal.mk_toType, ← Cardinal.ord_aleph 1, Cardinal.card_ord]

/-- The countable ordinals are uncountable. -/
instance instUncountableOmegaOne : Uncountable (OmegaOne.{u}) :=
  Cardinal.aleph0_lt_mk_iff.mp (mk_omegaOne.symm ▸ Cardinal.aleph0_lt_aleph_one)

/-- Every proper initial segment of the countable ordinals is countable: it has the cardinality
of its order type, which is a countable ordinal. -/
theorem countable_Iio_omegaOne (a : OmegaOne.{u}) : (Set.Iio a).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, ← not_lt, ← Cardinal.aleph_one_le_iff, not_le]
  have hcard : #(Set.Iio a) = (Ordinal.typein (α := OmegaOne.{u}) (· < ·) a).card := by
    rw [Ordinal.card_typein]
    rfl
  rw [hcard, ← Cardinal.lt_ord, Cardinal.ord_aleph 1]
  exact Ordinal.typein_lt_self a

/-- **The index of the construction is inhabited.** There is a type in any universe carrying a
well-order which is uncountable and all of whose proper initial segments are countable. -/
theorem exists_index :
    ∃ (I : Type u) (_ : LinearOrder I) (_ : WellFoundedLT I) (_ : Uncountable I),
      ∀ a : I, (Set.Iio a).Countable :=
  ⟨OmegaOne.{u}, inferInstance, inferInstance, inferInstance, countable_Iio_omegaOne⟩

end Stacks.Coherent

end
