module

public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The adic filtration by a principal ideal

Two facts about the filtration of a ring by the powers of a principal ideal `I = (π)`, used
wherever the `I`-adic completion is computed through the quotients `R / (π ^ n)`.

## Main results

* `Module.pow_smul_top_eq_span_pow`: the `n`-th step `I ^ n • ⊤` of the filtration, as a
  submodule of `R`, is the ideal `(π ^ n)`.
* `Module.mul_mem_span_pow_succ_iff`: multiplication by a nonzerodivisor shifts the filtration,
  so `π a` is divisible by `π ^ (n + 1)` exactly when `a` is divisible by `π ^ n`.
-/

@[expose] public section

namespace Module

/-- The `n`-th step `I ^ n • ⊤` of the adic filtration of `R` by a principal ideal `I = (π)`,
as a submodule of `R`, is the ideal `(π ^ n)`. -/
theorem pow_smul_top_eq_span_pow {R : Type*} [CommRing R] {I : Ideal R} {π : R}
    (hI : I = Ideal.span {π}) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R R) = Ideal.span {π ^ n} := by
  rw [hI, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.span_singleton_pow]

/-- Multiplication by a nonzerodivisor `π` shifts the filtration by powers of `π`: `π a` is
divisible by `π ^ (n + 1)` exactly when `a` is divisible by `π ^ n`. -/
theorem mul_mem_span_pow_succ_iff {R : Type*} [CommRing R] {π : R}
    (hπ : IsSMulRegular R π) {a : R} {n : ℕ} :
    π * a ∈ Ideal.span {π ^ (n + 1)} ↔ a ∈ Ideal.span {π ^ n} := by
  simp only [Ideal.mem_span_singleton']
  refine ⟨fun ⟨c, hc⟩ => ⟨c, hπ ?_⟩, fun ⟨c, hc⟩ => ⟨c, by rw [← hc]; ring⟩⟩
  simp only [smul_eq_mul]
  calc
    π * (c * π ^ n) = c * π ^ (n + 1) := by ring
    _ = π * a := hc

end Module

end
