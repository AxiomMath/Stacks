module

public import Mathlib.RingTheory.Ideal.Maximal
import StacksCore.Tactic.StacksAttribute

/-! ## Maximal ideals

Alongside the tag for `Ideal.exists_maximal`, this file carries the converse direction:
possessing a maximal ideal forces the ring to be nontrivial, so the two together characterise
nontriviality. Neither lemma is about local rings, but both are used in that development —
see `StacksCore.RingTheory.LocalRing.MaximalIdeal.Basic`.
-/

@[expose] public section

add_to_stacks 00E0 "2" Ideal.exists_maximal

/-- A ring with a maximal ideal is nontrivial: a maximal ideal is proper, so `1 ∉ m`, and in
the zero ring every ideal contains `1`.

`m` is implicit so that this is usable as `hm.nontrivial`. -/
lemma Ideal.IsMaximal.nontrivial {R : Type*} [Semiring R] {m : Ideal R} (hm : m.IsMaximal) :
    Nontrivial R := nontrivial_of_ne 0 1 fun H ↦ hm.ne_top (m.eq_top_iff_one.2 (H ▸ m.zero_mem))

/-- A ring is nontrivial if and only if it has a maximal ideal. Forwards is
`Ideal.exists_maximal` (Zorn); backwards is `Ideal.IsMaximal.nontrivial`. -/
lemma Ideal.nontrivial_iff_exists_maximal {R : Type*} [Semiring R] :
    Nontrivial R ↔ ∃ m : Ideal R, m.IsMaximal :=
  ⟨fun _ ↦ Ideal.exists_maximal R, fun ⟨_, hm⟩ ↦ hm.nontrivial⟩
