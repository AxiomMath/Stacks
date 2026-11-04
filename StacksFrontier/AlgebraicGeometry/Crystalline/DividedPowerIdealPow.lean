module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# A finitely generated divided power ideal containing `p` is nilpotent modulo `p ^ N`

Let `I` be an ideal of a commutative ring `A` carrying divided powers `γ`, and let `p` be a
positive integer.  For `x ∈ I` the identity `x ^ p = p! · γ_p(x)` shows `x ^ p ∈ p A`, hence
`x ^ (p N) ∈ p ^ N A`.  So `I` lies in the radical of `p ^ N A`, and if `I` is finitely generated —
for instance if `A` is Noetherian — some power of `I` lies in `p ^ N A`.  When `p ^ N A ⊆ I`, the
kernel `I / p ^ N A` of `A / p ^ N A ⟶ A / I` is therefore a nilpotent ideal; and `p` itself is
nilpotent in `A / p ^ N A`.

These are the facts that make the finite levels `S_N = Spec(A / p ^ N A)` of an affine divided
power base into nilpotent thickenings of the closed fibre `S₀ = Spec(A / I)`.

## Main results

* `DividedPowers.pow_mem_span_pow` — `x ^ (p N) ∈ p ^ N A` for `x ∈ I`.
* `DividedPowers.exists_pow_le_span_pow` and `DividedPowers.exists_pow_le_span_pow_of_noetherian`
  — some power of `I` lies in `p ^ N A`.
* `DividedPowers.isNilpotent_ker_factor_span_pow` — the kernel of `A / p ^ N A ⟶ A / I` is
  nilpotent.
* `isNilpotent_natCast_quotient_span_pow` — `p` is nilpotent in `A / p ^ N A`.

## References

* [Stacks Project, Tag 07GK](https://stacks.math.columbia.edu/tag/07GK)
-/

@[expose] public section

open Nat

namespace DividedPowers

variable {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {p : ℕ}

include hI in
/-- **`x ^ p ∈ p A` for `x` in a divided power ideal**: `x ^ p = p! · γ_p(x)` and `p ∣ p!`. -/
theorem pow_mem_span_natCast (hp : 0 < p) {x : A} (hx : x ∈ I) :
    x ^ p ∈ Ideal.span {(p : A)} := by
  rw [← hI.factorial_mul_dpow_eq_pow hx, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hp le_rfl
  exact ⟨c * hI.dpow p x, by rw [hc, cast_mul, mul_assoc]⟩

include hI in
/-- **`x ^ (p N) ∈ p ^ N A` for `x` in a divided power ideal.** -/
theorem pow_mem_span_pow (hp : 0 < p) (N : ℕ) {x : A} (hx : x ∈ I) :
    x ^ (p * N) ∈ Ideal.span {(p : A) ^ N} := by
  rw [pow_mul, ← Ideal.span_singleton_pow]
  exact Ideal.pow_mem_pow (hI.pow_mem_span_natCast hp hx) N

include hI in
/-- **A divided power ideal lies in the radical of `p ^ N A`.** -/
theorem le_radical_span_pow (hp : 0 < p) (N : ℕ) : I ≤ (Ideal.span {(p : A) ^ N}).radical :=
  fun _ hx ↦ ⟨p * N, hI.pow_mem_span_pow hp N hx⟩

include hI in
/-- **Some power of a finitely generated divided power ideal lies in `p ^ N A`.** -/
theorem exists_pow_le_span_pow (hfg : I.FG) (hp : 0 < p) (N : ℕ) :
    ∃ M : ℕ, I ^ M ≤ Ideal.span {(p : A) ^ N} :=
  Ideal.exists_pow_le_of_le_radical_of_fg (hI.le_radical_span_pow hp N) hfg

include hI in
/-- **Some power of a divided power ideal of a Noetherian ring lies in `p ^ N A`.** -/
theorem exists_pow_le_span_pow_of_noetherian [IsNoetherianRing A] (hp : 0 < p) (N : ℕ) :
    ∃ M : ℕ, I ^ M ≤ Ideal.span {(p : A) ^ N} :=
  hI.exists_pow_le_span_pow (IsNoetherian.noetherian I) hp N

include hI in
/-- **The kernel of `A / p ^ N A ⟶ A / I` is nilpotent** when `p ^ N A ⊆ I` and `I` is finitely
generated: it is the image of `I`, and some power of `I` lies in `p ^ N A`. -/
theorem isNilpotent_ker_factor_span_pow (hfg : I.FG) (hp : 0 < p) (N : ℕ)
    (h : Ideal.span {(p : A) ^ N} ≤ I) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  obtain ⟨M, hM⟩ := hI.exists_pow_le_span_pow hfg hp N
  refine ⟨M, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff]
  exact (Ideal.map_mono hM).trans (Ideal.map_quotient_self _).le

include hI in
/-- **The kernel of `A / p ^ N A ⟶ A / I` is nilpotent** for a divided power ideal
`I ⊇ p ^ N A` of a Noetherian ring. -/
theorem isNilpotent_ker_factor_span_pow_of_noetherian [IsNoetherianRing A] (hp : 0 < p) (N : ℕ)
    (h : Ideal.span {(p : A) ^ N} ≤ I) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) :=
  hI.isNilpotent_ker_factor_span_pow (IsNoetherian.noetherian I) hp N h

end DividedPowers

/-- **`p` is nilpotent in `A / p ^ N A`.** -/
theorem isNilpotent_natCast_quotient_span_pow {A : Type*} [CommRing A] (p N : ℕ) :
    IsNilpotent ((p : A ⧸ Ideal.span {(p : A) ^ N})) :=
  ⟨N, by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _⟩
