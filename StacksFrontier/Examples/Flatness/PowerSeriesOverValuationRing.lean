module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Flatness.CompletelyNormalOfPowerSeriesFlat
public import StacksFrontier.RingTheory.IntegralClosure.AlmostIntegral
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Valuation.Criteria

/-!
# Power series over a valuation ring of dimension at least two

For a valuation ring `R` which is a domain, `R⟦x⟧` is always a flat `R`-module, because `R` is
Bezout and `R⟦x⟧` is torsion-free over it. If moreover the Krull dimension of `R` exceeds one,
then `R⟦x⟧` is *not* flat over `R[x]`: the dimension hypothesis produces a nonzero prime `p`
which is not maximal, and from `x ∈ p`, `y ∉ p` with `y` in the maximal ideal one gets `yⁿ ∣ x`
for every `n`, so `y⁻¹` is almost integral over `R` without being in `R`. A valuation ring is
normal, so if `R⟦x⟧` were flat over `R[x]` then normality would force complete normality, which
`y⁻¹` contradicts.

## Main results

* `Stacks.Examples.instFlatPowerSeriesOfValuationRing`: the power series ring over a valuation
  ring is flat over the coefficient ring.
* `Stacks.Examples.not_flat_powerSeries_over_polynomial_of_dim_gt_one`: in Krull dimension
  greater than one it is not flat over the polynomial ring.

## Implementation notes

The two flatness assertions of the source are stated separately; both use the canonical module
structures on the power series ring.

## References

* [Stacks Project, Tag 0F1Z](https://stacks.math.columbia.edu/tag/0F1Z)
-/

@[expose] public section

namespace Stacks.Examples

open scoped nonZeroDivisors

/-- Power series over a domain are torsion-free over the coefficient ring. -/
private theorem powerSeries_isTorsionFree (R : Type*) [CommRing R] [IsDomain R] :
    Module.IsTorsionFree R (PowerSeries R) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a f h
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    ext n
    exact (mul_eq_zero.mp (show a * PowerSeries.coeff n f = 0 by
      simpa [PowerSeries.coeff_smul] using congrArg (PowerSeries.coeff n) h)).resolve_left ha

/-- The power series ring over a valuation ring is flat over its coefficient ring. -/
@[stacks 0F1Z "flat over the coefficient ring"]
instance instFlatPowerSeriesOfValuationRing (R : Type*) [CommRing R] [IsDomain R]
    [ValuationRing R] : Module.Flat R (PowerSeries R) := by
  let : Module.IsTorsionFree R (PowerSeries R) := powerSeries_isTorsionFree R
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- A valuation ring of Krull dimension greater than one has a nonzero prime that is not
maximal. -/
private theorem exists_nonzero_nonmaximal_prime_of_dim_gt_one
    (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    (hdim : 1 < ringKrullDim R) :
    ∃ p : Ideal R, p ≠ ⊥ ∧ p.IsPrime ∧ ¬ p.IsMaximal := by
  by_contra h
  refine not_lt_of_ge (Ring.krullDimLE_iff.mp ?_) hdim
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
  exact fun p hpb hp => not_not.mp fun hpm => h ⟨p, hpb, hp, hpm⟩

/-- In Krull dimension greater than one a valuation ring is not completely normal: there is an
almost integral element of its fraction field outside the ring. -/
private theorem exists_almostIntegral_not_mem_of_dim_gt_one
    (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    (hdim : 1 < ringKrullDim R) :
    ∃ g : FractionRing R,
      IsAlmostIntegral R g ∧ g ∉ (algebraMap R (FractionRing R)).range := by
  obtain ⟨p, hpbot, hp, hpmax⟩ := exists_nonzero_nonmaximal_prime_of_dim_gt_one R hdim
  have : IsLocalRing R := (ValuationRing.iff_local_bezout_domain.mp
    (inferInstance : ValuationRing R)).1
  have hpm : p < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p) fun h =>
      hpmax (h ▸ inferInstance)
  obtain ⟨x, hx, hx0⟩ := p.ne_bot_iff.mp hpbot
  obtain ⟨y, hym, hyp⟩ := Set.not_subset.1 hpm.2
  have hy0 : y ≠ 0 := fun hy => hyp (hy ▸ p.zero_mem)
  let K := FractionRing R
  let g : K := (algebraMap R K y)⁻¹
  have hyK : algebraMap R K y ≠ 0 := fun h => hy0 (IsFractionRing.injective R K (by simpa using h))
  have hdiv : ∀ n : ℕ, y ^ n ∣ x := fun n => by
    rcases ValuationRing.dvd_total (x := x) (y := y ^ n) with ⟨a, ha⟩ | hyx
    · exact (hyp (hp.mem_of_pow_mem n (ha ▸ p.mul_mem_right a hx))).elim
    · exact hyx
  refine ⟨g, ?_, ?_⟩
  · change ∃ r ∈ R⁰, ∀ n, r • g ^ n ∈ (algebraMap R K).range
    refine ⟨x, by simpa [mem_nonZeroDivisors_iff_ne_zero] using hx0, fun n => ?_⟩
    obtain ⟨a, ha⟩ := hdiv n
    change ∃ b : R, algebraMap R K b = x • g ^ n
    refine ⟨a, ?_⟩
    rw [Algebra.smul_def]
    dsimp [g]
    calc
      algebraMap R K a = (algebraMap R K y ^ n)⁻¹ *
          (algebraMap R K y ^ n * algebraMap R K a) := by
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hyK), one_mul]
      _ = (algebraMap R K y ^ n)⁻¹ * algebraMap R K x := by
        rw [← map_pow, ← map_mul, ← ha]
      _ = algebraMap R K x * (algebraMap R K y)⁻¹ ^ n := by
        rw [inv_pow]
        ring
  · rintro ⟨a, ha⟩
    have hya : y * a = 1 := (IsFractionRing.injective R K) (by
      rw [map_mul, ha]
      simpa [g] using mul_inv_cancel₀ hyK)
    exact IsLocalRing.notMem_maximalIdeal.2 (.of_mul_eq_one a hya) hym

/-- In dimension greater than one, the power series ring over a valuation ring is not
flat over its polynomial ring. -/
@[stacks 0F1Z "not flat over the polynomial ring"]
theorem not_flat_powerSeries_over_polynomial_of_dim_gt_one (R : Type*)
    [CommRing R] [IsDomain R] [ValuationRing R] (hdim : 1 < ringKrullDim R) :
    ¬ Module.Flat (Polynomial R) (PowerSeries R) := by
  intro hflat
  obtain ⟨g, hg, hgn⟩ := exists_almostIntegral_not_mem_of_dim_gt_one R hdim
  exact hgn (((normal_iff_isCompletelyNormal_of_powerSeries_flat R hflat).mp
    (valuationRing_isIntegrallyClosed R)) g hg)

end Stacks.Examples

end
