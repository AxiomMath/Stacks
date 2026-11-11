module

public import Mathlib.RingTheory.Polynomial.SeparableDegree
public import StacksCore.FieldTheory.Separable
import StacksCore.Tactic.StacksAttribute

/-!
# Irreducible polynomials: separable or a separable polynomial in `x ^ (p ^ m)`

[stacks, 09H0]: let `F` be a field and `P ∈ F[x]` irreducible. Then either `P` and `P'` are
relatively prime, or `P' = 0`. The second case only happens if `F` has characteristic `p > 0`,
and then `P(x) = Q(x ^ q)` with `q = p ^ m` a power of `p` and `Q ∈ F[x]` an irreducible
polynomial relatively prime to `Q'`.

## Main results

* `Irreducible.eq_expand_of_derivative_eq_zero`: the third part of [stacks, 09H0].
* `Irreducible.isCoprime_derivative_or_eq_expand`: the full statement of [stacks, 09H0].
-/

@[expose] public section

open Polynomial

namespace Irreducible

variable {F : Type*} [Field F] {P : F[X]}

/-- **Stacks 09H0** (third part). If `P ∈ F[x]` is irreducible with `P' = 0`, then `F` has
prime characteristic `p` and `P(x) = Q(x ^ (p ^ m))` for some `m ≥ 1` and some irreducible
`Q ∈ F[x]` relatively prime to its derivative `Q'`. -/
@[stacks 09H0 "third part"]
theorem eq_expand_of_derivative_eq_zero (hP : Irreducible P) (hd : derivative P = 0) :
    ∃ p, p.Prime ∧ CharP F p ∧ ∃ m, 1 ≤ m ∧ ∃ Q : F[X],
      Irreducible Q ∧ IsCoprime Q (derivative Q) ∧ expand F (p ^ m) Q = P := by
  have hns : ¬P.Separable := fun hs ↦ hP.not_isUnit <| by
    rwa [Separable, hd, isCoprime_zero_right] at hs
  obtain ⟨p, hp, hpc⟩ := charP_prime_of_not_separable hP hns
  have : ExpChar F p := ExpChar.prime hp
  obtain ⟨Q, hQs, m, hQ⟩ := hP.hasSeparableContraction p
  refine ⟨p, hp, hpc, m, Nat.one_le_iff_ne_zero.mpr ?_, Q,
    of_irreducible_expand (pow_ne_zero _ hp.ne_zero) (hQ ▸ hP), hQs, hQ⟩
  rintro rfl
  rw [pow_zero, expand_one] at hQ
  exact hns (hQ ▸ hQs)

/-- **Stacks 09H0**. Let `P ∈ F[x]` be irreducible. Then either `P` and `P'` are relatively
prime, or `P' = 0`; and in the second case `F` has prime characteristic `p` and
`P(x) = Q(x ^ (p ^ m))` for some `m ≥ 1` and some irreducible `Q ∈ F[x]` relatively prime to
its derivative `Q'`. -/
@[stacks 09H0]
theorem isCoprime_derivative_or_eq_expand (hP : Irreducible P) :
    (IsCoprime P (derivative P) ∨ derivative P = 0) ∧
      (derivative P = 0 → ∃ p, p.Prime ∧ CharP F p ∧ ∃ m, 1 ≤ m ∧ ∃ Q : F[X],
        Irreducible Q ∧ IsCoprime Q (derivative Q) ∧ expand F (p ^ m) Q = P) :=
  ⟨or_iff_not_imp_right.mpr fun hd ↦ (separable_iff_derivative_ne_zero hP).mpr hd,
    hP.eq_expand_of_derivative_eq_zero⟩

end Irreducible
