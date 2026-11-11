module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Purely inseparable extensions in the sense of the Stacks Project

Stacks 030J (3) calls an algebraic extension `K/k` *purely inseparable* if the characteristic
of `k` is `p > 0` and every `α ∈ K` has a power `α ^ q`, with `q` a power of `p`, lying in `k`.
Mathlib's `IsPurelyInseparable k K` asks instead that `K/k` be integral and that every element
of `K` separable over `k` lie in `k`; it makes no demand on the characteristic.

The two agree in characteristic `p > 0` (`isPurelyInseparableStacks_iff_isPurelyInseparable`),
and differ in characteristic zero: there Stacks' notion never holds
(`not_isPurelyInseparableStacks_of_charZero`), while Mathlib's holds exactly when
`algebraMap k K` is surjective, i.e. `K = k`
(`isPurelyInseparable_iff_surjective_algebraMap_of_charZero`). In general Stacks' notion is
Mathlib's together with `ringChar k ≠ 0`
(`isPurelyInseparableStacks_iff_isPurelyInseparable_and_ringChar_ne_zero`).
-/

@[expose] public section

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- **Stacks 030J (3).** An algebraic extension `K/k` is *purely inseparable* in the sense of the
Stacks Project if the characteristic of `k` is some `p > 0` and for every `α ∈ K` there is a
power `q = p ^ n` of `p` with `α ^ q ∈ k`. Unlike Mathlib's `IsPurelyInseparable`, this is
never satisfied in characteristic zero. -/
@[stacks 030J "item (3), purely inseparable, in Stacks' own form: algebraic, characteristic
  `p > 0`, and a `p`-power power of every element lies in `k`"]
def IsPurelyInseparableStacks : Prop :=
  Algebra.IsAlgebraic k K ∧ ∃ p : ℕ, 0 < p ∧ CharP k p ∧
    ∀ α : K, ∃ n : ℕ, α ^ p ^ n ∈ (algebraMap k K).range

/-- **Stacks 030J (3)**, bridge to Mathlib. If `k` has characteristic a prime `p`, then `K/k` is
purely inseparable in the sense of the Stacks Project if and only if it is so in Mathlib's sense
`IsPurelyInseparable k K`. -/
@[stacks 030J "item (3): in characteristic `p > 0` Stacks' notion is Mathlib's
  `IsPurelyInseparable`"]
theorem isPurelyInseparableStacks_iff_isPurelyInseparable (p : ℕ) [hp : Fact p.Prime]
    [CharP k p] : IsPurelyInseparableStacks k K ↔ IsPurelyInseparable k K := by
  rw [isPurelyInseparable_iff_pow_mem k p]
  constructor
  · rintro ⟨-, p', -, hc, h⟩
    obtain rfl := CharP.eq k hc ‹CharP k p›
    exact h
  · intro h
    have : IsPurelyInseparable k K := (isPurelyInseparable_iff_pow_mem k p).2 h
    exact ⟨IsPurelyInseparable.isAlgebraic k K, p, hp.out.pos, ‹_›, h⟩

/-- **Stacks 030J (3)**, characteristic zero. Over a field of characteristic zero no extension is
purely inseparable in the sense of the Stacks Project. -/
@[stacks 030J "item (3): in characteristic zero Stacks' notion never holds"]
theorem not_isPurelyInseparableStacks_of_charZero [CharZero k] :
    ¬ IsPurelyInseparableStacks k K := by
  rintro ⟨-, p, hp, hc, -⟩
  exact hp.ne' (CharP.eq k hc (CharP.ofCharZero k))

/-- In characteristic zero, Mathlib's `IsPurelyInseparable k K` holds exactly when
`algebraMap k K` is surjective, i.e. when `K = k`; compare
`not_isPurelyInseparableStacks_of_charZero`. -/
@[stacks 030J "item (3): in characteristic zero Mathlib's `IsPurelyInseparable` means `K = k`"]
theorem isPurelyInseparable_iff_surjective_algebraMap_of_charZero [CharZero k] :
    IsPurelyInseparable k K ↔ Function.Surjective (algebraMap k K) := by
  simp [isPurelyInseparable_iff_pow_mem k 1, RingHom.mem_range, Function.Surjective]

/-- **Stacks 030J (3)**, in every characteristic: `K/k` is purely inseparable in the sense of
the Stacks Project if and only if it is so in Mathlib's sense and `k` has positive
characteristic. -/
@[stacks 030J "item (3): Stacks' notion is Mathlib's `IsPurelyInseparable` plus positive
  characteristic"]
theorem isPurelyInseparableStacks_iff_isPurelyInseparable_and_ringChar_ne_zero :
    IsPurelyInseparableStacks k K ↔ IsPurelyInseparable k K ∧ ringChar k ≠ 0 := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | h0
  · have : Fact (ringChar k).Prime := ⟨hp⟩
    rw [isPurelyInseparableStacks_iff_isPurelyInseparable k K (ringChar k)]
    exact ⟨fun h ↦ ⟨h, hp.ne_zero⟩, And.left⟩
  · have : CharZero k := (CharP.charP_zero_iff_charZero k).1 (h0 ▸ ringChar.charP k)
    exact ⟨fun h ↦ (not_isPurelyInseparableStacks_of_charZero k K h).elim,
      fun h ↦ (h.2 h0).elim⟩
