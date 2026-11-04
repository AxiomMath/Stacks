module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Derivation.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derivations kill `p`-th powers in characteristic `p`

Over a ring of characteristic `p`, every derivation annihilates every `p`-th power.

## Main results

* `Derivation.map_pow_char_eq_zero`: a derivation of an algebra of characteristic `p` sends
  `x ^ p` to `0`.
-/

@[expose] public section

/-- In characteristic `p` a derivation kills `p`-th powers: `D (x ^ p) = 0`. -/
@[ega "0 21.1.5" "(i)"]
public lemma Derivation.map_pow_char_eq_zero {R A M : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module A M] [Module R M] (D : Derivation R A M) (p : ℕ)
    [CharP A p] (x : A) : D (x ^ p) = 0 := by
  rw [D.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero, zero_smul]

end
