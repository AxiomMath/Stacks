module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness

/-!
# Finiteness over `ℤ_[p]` of a complete local `ℤ_[p]`-algebra with finite special fibre

Let `R` be a local `ℤ_[p]`-algebra which is complete for the topology defined by the powers of
its maximal ideal, and in which `p` is not invertible. If the special fibre `R/pR` is a finite
set, then `R` is a finite `ℤ_[p]`-module.

The input is Stacks Tag 031D: a module over a precomplete ring which is separated for the adic
filtration and has finite reduction is finite. Here the ring is `ℤ_[p]`, precomplete for its
maximal ideal, and the separatedness of `R` for the `p`-adic filtration follows from its
separatedness for the `𝔪_R`-adic one because `p` lies in `𝔪_R`.

## Main results

* `PadicInt.finite_of_isAdicComplete_of_finite_quotient` — a complete local `ℤ_[p]`-algebra with
  finite special fibre is finite over `ℤ_[p]`.

## References

* [Stacks Project, Tag 031D](https://stacks.math.columbia.edu/tag/031D)
-/

@[expose] public noncomputable section

universe u

namespace PadicInt

/-- A local `ℤ_[p]`-algebra `R` which is complete for the topology defined by the powers of its
maximal ideal, in which `p` is not invertible, and whose special fibre `R/pR` is finite, is a
finite `ℤ_[p]`-module.

Since `p` is a non-unit of the local ring `R` it lies in `𝔪_R`, so `pⁿR ⊆ 𝔪_Rⁿ` and the
`𝔪_R`-adic separatedness supplied by completeness gives `⋂ₙ pⁿR = 0`. Stacks Tag 031D then
applies with the ring `ℤ_[p]`, which is precomplete for its maximal ideal `(p)`. -/
public theorem finite_of_isAdicComplete_of_finite_quotient {p : ℕ} [Fact p.Prime] (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (hp : ¬ IsUnit (algebraMap ℤ_[p] R (p : ℤ_[p])))
    (hfin : Finite (R ⧸ (IsLocalRing.maximalIdeal ℤ_[p] • (⊤ : Submodule ℤ_[p] R)))) :
    Module.Finite ℤ_[p] R := by
  have := hfin
  have hmem : algebraMap ℤ_[p] R (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal _).2 hp
  refine Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
    (IsLocalRing.maximalIdeal ℤ_[p]) ?_ Module.Finite.of_finite
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine hc.toIsHausdorff.haus' x fun n => ?_
  rw [SModEq.zero]
  have hxn : x ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] R) :=
    (Submodule.mem_iInf _).1 hx n
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hxn
  obtain ⟨y, -, hy⟩ := hxn
  have htop : (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R R)
      = (IsLocalRing.maximalIdeal R) ^ n := by simp
  rw [htop, ← hy, Algebra.smul_def, map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hmem n)

end PadicInt

end
