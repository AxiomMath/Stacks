module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import StacksFrontier.RingTheory.Polynomial.StepanovBound

/-!
# Points of an absolutely irreducible plane curve avoiding a second curve

Let `f, g ∈ F[x, y]` over a finite field `F`, with `f` irreducible over an algebraic closure of
`F`, of total degree at most `d`, `g` of total degree at most `e`, and `f ∤ g`. If `F` has more
than some `N(d, e)` elements, there is a point of `F²` where `f` vanishes and `g` does not.

The Weil lower bound gives at least `q - c(d) √q` zeros of `f` in `F²`, where `q = #F`, and by a
weak form of Bézout's theorem at most `2 max(d, e)³` of them are zeros of `g`.

## Main results

* `MvPolynomial.exists_eval_eq_zero_and_eval_ne_zero_of_irreducible_map_algebraicClosure`.
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- **Points of an absolutely irreducible plane curve off a second curve.** For all `d, e` there
is `N` such that over every finite field `F` with more than `N` elements, every `f, g ∈ F[x, y]` of
total degrees at most `d` and `e`, with `f` irreducible over an algebraic closure of `F` and
`f ∤ g`, have a common point with `f = 0` and `g ≠ 0`. -/
theorem exists_eval_eq_zero_and_eval_ne_zero_of_irreducible_map_algebraicClosure (d e : ℕ) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F], N < Fintype.card F →
      ∀ f g : MvPolynomial (Fin 2) F, f.totalDegree ≤ d → g.totalDegree ≤ e →
        Irreducible (f.map (algebraMap F (AlgebraicClosure F))) → ¬ f ∣ g →
          ∃ x : Fin 2 → F, MvPolynomial.eval x f = 0 ∧ MvPolynomial.eval x g ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_card_zeroSet_ge_of_absolutelyIrreducible.{u} d
  set D := max d e
  set B : ℝ := |c| + 2 * D ^ 3 + 1
  have hB : 0 ≤ B := by positivity
  refine ⟨⌈B ^ 2⌉₊, fun F _ _ hF f g hf hg hirr hfg => ?_⟩
  by_contra! h
  -- Every zero of `f` is a zero of `g`, and there are at most `2 D³` common zeros.
  obtain ⟨hfin, hcard⟩ := finite_zeroSet_inter_of_not_dvd
    (irreducible_of_irreducible_map _ hirr) hfg (hf.trans (le_max_left d e))
    (hg.trans (le_max_right d e))
  have hle : {p : Fin 2 → F | eval p f = 0}.ncard ≤
      {p : Fin 2 → F | eval p f = 0 ∧ eval p g = 0}.ncard :=
    Set.ncard_le_ncard (fun p (hp : eval p f = 0) => ⟨hp, h p hp⟩) hfin
  have hupper : ({p : Fin 2 → F | eval p f = 0}.ncard : ℝ) ≤ 2 * D ^ 3 := by
    exact_mod_cast hle.trans hcard
  -- But there are at least `q - c √q > 2 D³` zeros of `f`.
  have hlower := hc F f hf hirr
  have hq : B ^ 2 < (Fintype.card F : ℝ) := by
    have : (⌈B ^ 2⌉₊ : ℝ) < Fintype.card F := by exact_mod_cast hF
    exact (Nat.le_ceil _).trans_lt this
  set q : ℝ := (Fintype.card F : ℝ)
  have hs : B < √q := Real.lt_sqrt hB |>.mpr hq
  have hss : √q * √q = q := Real.mul_self_sqrt (by positivity)
  have hcs : c * √q ≤ |c| * √q := mul_le_mul_of_nonneg_right (le_abs_self c) (Real.sqrt_nonneg q)
  have hD : (0 : ℝ) ≤ 2 * D ^ 3 := by positivity
  nlinarith [abs_nonneg c]

end MvPolynomial
