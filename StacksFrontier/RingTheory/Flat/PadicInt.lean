module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness over the `p`-adic integers

A module over `ℤ_[p]` is flat exactly when it is torsion free, because `ℤ_[p]` is a discrete
valuation ring and hence a Bézout domain. Every nonzero element of `ℤ_[p]` is a unit times a
power of `p`, so torsion freeness is already implied by the single condition that `p` act
injectively.

## Main results

* `PadicInt.flat_of_forall_smul_eq_zero` — a `ℤ_[p]`-module on which multiplication by `p` is
  injective is flat.

## References

* [Stacks Project, Tag 00H9](https://stacks.math.columbia.edu/tag/00H9) for flatness over a
  principal ideal domain
-/

@[expose] public section

namespace PadicInt

/-- A `ℤ_[p]`-module on which multiplication by `p` is injective is flat.

Flatness over the Bézout domain `ℤ_[p]` is torsion freeness, and a nonzero `a : ℤ_[p]` is a unit
times `p ^ a.valuation`, so an element killed by `a` is killed by a power of `p`. -/
public theorem flat_of_forall_smul_eq_zero {p : ℕ} [Fact p.Prime] {M : Type*}
    [AddCommGroup M] [Module ℤ_[p] M]
    (h : ∀ x : M, (p : ℤ_[p]) • x = 0 → x = 0) : Module.Flat ℤ_[p] M := by
  have hpow : ∀ (m : ℕ) (x : M), ((p : ℤ_[p]) ^ m) • x = 0 → x = 0 := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      refine fun x hx => ih x (h _ ?_)
      rw [← mul_smul, ← pow_succ']
      exact hx
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨a, ha⟩ := hx
  have hane : (a : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero a
  rw [Submodule.mem_bot]
  set u := PadicInt.unitCoeff hane with hu
  refine hpow (a : ℤ_[p]).valuation x ?_
  have h1 : ((u : ℤ_[p]) * (p : ℤ_[p]) ^ (a : ℤ_[p]).valuation) • x = 0 := by
    rw [← PadicInt.unitCoeff_spec hane]; exact ha
  have h2 : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) •
      (((u : ℤ_[p]) * (p : ℤ_[p]) ^ (a : ℤ_[p]).valuation) • x) = 0 := by
    rw [h1, smul_zero]
  rwa [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at h2

end PadicInt

end
