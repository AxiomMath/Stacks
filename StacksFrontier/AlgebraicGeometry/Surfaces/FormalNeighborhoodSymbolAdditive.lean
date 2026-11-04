module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbol

/-!
# Consequences of additivity of a symbol map

Vanishing at `0`, additivity on differences and additivity on finite sums use nothing of a symbol
system beyond additivity on one step of the filtration, so they are stated here for a bare
filtration-and-symbol pair.

## Main results

* `AlgebraicGeometry.SemistableReduction.symbol_zero_of_add`,
  `AlgebraicGeometry.SemistableReduction.symbol_sub_of_add` and
  `AlgebraicGeometry.SemistableReduction.symbol_sum_range_of_add`.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace AlgebraicGeometry.SemistableReduction

/-! ### Consequences of additivity alone

Vanishing at `0`, additivity on differences and additivity on finite sums use no axiom of a
symbol system beyond additivity on one step of the filtration, so they are stated here for a bare
filtration-and-symbol pair.  Two structures of this development supply that additivity —
`AlgebraicGeometry.SemistableReduction.MonomialSymbol` below and
`AlgebraicGeometry.SemistableReduction.OneStepSymbol`, which presents multiplicativity as a
one-step law instead of a general bidegree law — and both reach these three facts through their
own `symbol_add` field rather than through a copy of the proof. -/

section SymbolAdd

variable {A : Type u} [CommRing A] {k : Type u} [CommRing k] {I : ℕ → Ideal A}
  {σ : ℕ → A → MvPolynomial (Fin 2) k}
  (hadd : ∀ (n : ℕ) {a b : A}, a ∈ I n → b ∈ I n → σ n (a + b) = σ n a + σ n b)

include hadd in
/-- A symbol map additive on `Iₙ` sends `0` to `0`. -/
theorem symbol_zero_of_add (n : ℕ) : σ n 0 = 0 := by
  have h := hadd n (zero_mem (I n)) (zero_mem (I n))
  rw [add_zero] at h
  linear_combination -h

include hadd in
/-- A symbol map additive on `Iₙ` is additive on differences inside `Iₙ`. -/
theorem symbol_sub_of_add (n : ℕ) {a b : A} (ha : a ∈ I n) (hb : b ∈ I n) :
    σ n (a - b) = σ n a - σ n b := by
  have h := hadd n (sub_mem ha hb) hb
  rw [sub_add_cancel] at h
  rw [h]
  ring

include hadd in
/-- A symbol map additive on `Iₙ` is additive on finite sums inside `Iₙ`. -/
theorem symbol_sum_range_of_add (n : ℕ) : ∀ (N : ℕ) (f : ℕ → A),
    (∀ j ∈ Finset.range N, f j ∈ I n) →
    σ n (∑ j ∈ Finset.range N, f j) = ∑ j ∈ Finset.range N, σ n (f j) := by
  intro N
  induction N with
  | zero => intro f _; simpa using symbol_zero_of_add hadd n
  | succ N ih =>
    intro f hf
    have hsub : ∀ j ∈ Finset.range N, f j ∈ I n := fun j hj =>
      hf j (Finset.mem_range.2 ((Finset.mem_range.1 hj).trans (Nat.lt_succ_self N)))
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      hadd n (Submodule.sum_mem _ hsub) (hf N (Finset.mem_range.2 (Nat.lt_succ_self N))),
      ih f hsub]

end SymbolAdd

end AlgebraicGeometry.SemistableReduction

