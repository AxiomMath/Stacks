module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyTracePowers
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeightsFromTraceGrowth

/-!
# Real characteristic polynomials and real traces

In the realizability argument of the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Weil II 1.5, Kedlaya §6) the Frobenius
characteristic polynomial of `F ⊕ F'` at a closed point is asked to have real coefficients along an
embedding `ι : K →+* ℂ`, while the trace formula on the fibres produces real traces.  The two are
equivalent in characteristic zero: the coefficients are polynomials in the power traces (Newton's
identities, `Stacks.EtaleCohomology.coeff_charpoly_map_mem_range_ofReal_of_trace_pow`), and
conversely the power traces are the power sums of the complex roots, whose multiset is stable
under complex conjugation when the polynomial is real.

## Main results

* `Stacks.EtaleCohomology.map_trace_pow_mem_range_ofReal_of_coeff`: real characteristic
  polynomial along `ι` ⇒ real traces of all powers.
* `Stacks.EtaleCohomology.coeff_charpoly_mul_mem_range_ofReal_iff`: for a pair of endomorphisms,
  the product of the characteristic polynomials is real along `ι` exactly when the sums of the
  traces of the powers are.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.EtaleCohomology

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **A real characteristic polynomial has real power traces.**  If the characteristic polynomial
of `f` has coefficients which `ι` maps into `ℝ`, so does every trace `Tr(f ^ n)`: it is the `n`-th
power sum of the complex roots, whose multiset is stable under complex conjugation. -/
theorem map_trace_pow_mem_range_ofReal_of_coeff (ι : K →+* ℂ) (f : Module.End K V)
    (h : ∀ j, ι (f.charpoly.coeff j) ∈ Set.range ((↑) : ℝ → ℂ)) (n : ℕ) :
    ι (LinearMap.trace K V (f ^ n)) ∈ Set.range ((↑) : ℝ → ℂ) := by
  set P := f.charpoly.map ι
  have hP : P.map (starRingEnd ℂ) = P := by
    ext j
    rw [coeff_map, coeff_map]
    obtain ⟨c, hc⟩ := h j
    rw [← hc, Complex.conj_ofReal]
  have hroots : P.roots.map (starRingEnd ℂ) = P.roots := by
    conv_rhs => rw [← hP]
    exact ((IsAlgClosed.splits P).roots_map_of_injective
      (starRingEnd ℂ).injective).symm
  rw [map_trace_pow_eq_sum_roots_map_pow]
  have key : (starRingEnd ℂ) ((P.roots.map (· ^ n)).sum) = (P.roots.map (· ^ n)).sum := by
    rw [map_multiset_sum, Multiset.map_map]
    conv_rhs => rw [← hroots, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    simp
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 key
  exact ⟨r, hr.symm⟩

/-- **Realizability of a pair in trace form.**  The product of the characteristic polynomials of
`f` and `g` has coefficients real along `ι` exactly when every `Tr(f ^ n) + Tr(g ^ n)` does:
both statements are about `f ⊕ g`. -/
theorem coeff_charpoly_mul_mem_range_ofReal_iff [CharZero K] (ι : K →+* ℂ) (f : Module.End K V)
    (g : Module.End K W) :
    (∀ j, ι ((f.charpoly * g.charpoly).coeff j) ∈ Set.range ((↑) : ℝ → ℂ)) ↔
      ∀ n, 1 ≤ n → ι (LinearMap.trace K V (f ^ n) + LinearMap.trace K W (g ^ n)) ∈
        Set.range ((↑) : ℝ → ℂ) := by
  have hpow : ∀ n, (f.prodMap g) ^ n = (f ^ n).prodMap (g ^ n) := fun n => by
    induction n with
    | zero => simp [pow_zero, LinearMap.prodMap_one]
    | succ n ih => rw [pow_succ, ih, pow_succ, pow_succ, LinearMap.prodMap_mul]
  have htr : ∀ n, LinearMap.trace K (V × W) ((f.prodMap g) ^ n) =
      LinearMap.trace K V (f ^ n) + LinearMap.trace K W (g ^ n) := fun n => by
    rw [hpow, LinearMap.trace_prodMap']
  rw [← LinearMap.charpoly_prodMap]
  exact ⟨fun h n _ => htr n ▸ map_trace_pow_mem_range_ofReal_of_coeff ι _ h n, fun h j =>
    coeff_charpoly_map_mem_range_ofReal_of_trace_pow ι _ (fun n hn => htr n ▸ h n hn) j⟩

end Stacks.EtaleCohomology
