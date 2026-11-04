module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finite extensions of a finite field inside an algebraic closure

Let `k` be a finite field with `p ^ q` elements and `k̄` an algebraically closed field containing
`k`. For every `n ≥ 1` there is an intermediate field `k ⊆ k_n ⊆ k̄` with `p ^ (q n)` elements, of
degree `n` over `k`: the image of a `k`-embedding of the Galois field `𝔽_{p ^ (q n)}` into `k̄`.
These are the fields `k_n` over which the trace formula is applied to obtain the traces of the
powers of Frobenius in [Stacks, Tag 03UZ].

## Main results

* `FiniteField.exists_intermediateField_card_eq_pow`.
-/

@[expose] public section

namespace FiniteField

/-- **A finite extension of degree `n` of a finite field inside an algebraic closure.** -/
theorem exists_intermediateField_card_eq_pow (k : Type*) [Field k] [Fintype k] (kbar : Type*)
    [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [hp : Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) {n : ℕ} (hn : 0 < n) :
    ∃ k' : IntermediateField k kbar, Nat.card k' = p ^ (q * n) ∧
      Module.finrank k k' = n := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero fun h =>
    (Fintype.one_lt_card (α := k)).ne' (by rw [hcard, h, pow_zero])
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have hk : Module.finrank (ZMod p) k = q := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := k)
    rw [hcard, ZMod.card] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  have hqn : q * n ≠ 0 := (Nat.mul_pos hq hn).ne'
  let GF := GaloisField p (q * n)
  have hGF : Module.finrank (ZMod p) GF = q * n := GaloisField.finrank p hqn
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := k) (L := GF)
    (by rw [hk, hGF]; exact dvd_mul_right q n)
  let : Algebra k GF := φ.toRingHom.toAlgebra
  have : Module.Finite k GF := Module.Finite.of_finite
  have : Algebra.IsAlgebraic k GF := Algebra.IsAlgebraic.of_finite k GF
  let ψ : GF →ₐ[k] kbar := IsAlgClosed.lift
  let e : GF ≃ₐ[k] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hcardGF : Nat.card GF = p ^ (q * n) := GaloisField.card p (q * n) hqn
  refine ⟨ψ.fieldRange, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv, hcardGF]
  · rw [← e.toLinearEquiv.finrank_eq]
    let := Fintype.ofFinite GF
    have h := Module.card_eq_pow_finrank (K := k) (V := GF)
    rw [← Nat.card_eq_fintype_card, hcardGF, hcard, ← pow_mul] at h
    exact (Nat.mul_left_cancel hq (Nat.pow_right_injective hp.out.two_le h)).symm

end FiniteField
