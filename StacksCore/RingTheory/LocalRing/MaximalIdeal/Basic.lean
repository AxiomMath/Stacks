module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksCore.RingTheory.Ideal.Maximal
import StacksCore.Tactic.StacksAttribute

/-! # A local ring has exactly one maximal ideal

Stacks tag 07BI defines a local ring as one with *exactly one* maximal ideal, whereas Mathlib's
`IsLocalRing` is the condition that the ring is nontrivial and `a` or `b` is a unit whenever
`a + b = 1`. `IsLocalRing.maximal_ideal_unique` is the Stacks-facing form, `∃! I, I.IsMaximal`,
and so records the definition in the tag's own words; `IsLocalRing.of_unique_max_ideal` is the
converse.

This is the reason the tag sits on two declarations rather than one — see
`StacksCore.RingTheory.LocalRing.Defs`.

This file also carries clause (1) ⇔ (3) of tag 00E9: locality is equivalent to the existence of
a maximal ideal outside which everything is a unit. Note this is *not* the same as
`IsLocalRing.of_unique_max_ideal`, which asks for uniqueness of the maximal ideal; here a single
maximal ideal is produced and uniqueness is a consequence rather than a hypothesis.
-/

@[expose] public section

add_to_stacks 07BI "`∃! I, I.IsMaximal` — the Stacks project's own phrasing of the definition
  of a local ring, which Mathlib derives from its `a + b = 1` formulation."
  IsLocalRing.maximal_ideal_unique

open IsLocalRing

/-- **Stacks 00E9**, clause (1) ⇔ (3): a ring is local if and only if it has a maximal ideal
`m` such that every element outside `m` is a unit.

The forward direction takes `m` to be `IsLocalRing.maximalIdeal R`, where being outside `m` is
*definitionally* being a unit (`IsLocalRing.notMem_maximalIdeal`). The reverse direction cannot
use `IsLocalRing.of_unique_max_ideal` directly — that wants uniqueness, which is not assumed —
so it goes through `IsLocalRing.of_nonunits_add`: the hypothesis says every nonunit lies in `m`,
and `m` is closed under addition. Nontriviality comes from `m ≠ ⊤`. -/
@[stacks 00E9 "(1) ⇔ (3)"]
theorem isLocalRing_iff_exists_maximal_isUnit {R : Type*} [CommSemiring R] :
    IsLocalRing R ↔ ∃ m : Ideal R, m.IsMaximal ∧ ∀ x : R, x ∉ m → IsUnit x := by
  refine ⟨fun _ ↦ ⟨maximalIdeal R, maximalIdeal.isMaximal R, fun _ h ↦ notMem_maximalIdeal.1 h⟩,
    fun ⟨m, hm, h⟩ ↦ have := hm.nontrivial; of_nonunits_add fun a b ha hb hu => ?_⟩
  refine hm.ne_top (m.eq_top_of_isUnit_mem (m.add_mem ?_ ?_) hu) <;> by_contra hc <;> simp_all
