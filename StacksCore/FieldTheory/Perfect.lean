module

public import Mathlib.FieldTheory.Perfect

/-! # Perfect fields -/

@[expose] public section

open Polynomial

/-- **Stacks 09H4**.
Over a perfect ring `S` of exponential characteristic `p`, the polynomial `f.expand R p`
and `f` have the same number of distinct roots in `S`: the Frobenius bijection on `S`
identifies the root sets. -/
@[stacks 09H4]
theorem Polynomial.card_toFinset_aroots_expand
    {R : Type*} [CommRing R]
    (S : Type*) [CommRing S] [IsDomain S] [DecidableEq S] [Algebra R S]
    {p : ℕ} [ExpChar S p] [PerfectRing S p] {f : R[X]} :
    ((f.expand R p).aroots S).toFinset.card = (f.aroots S).toFinset.card := by
  rw [aroots, aroots, ← roots_expand_image_frobenius (f := f.map _) (p := p),
    Finset.card_image_of_injective _ (frobenius_inj _ _), map_expand]
