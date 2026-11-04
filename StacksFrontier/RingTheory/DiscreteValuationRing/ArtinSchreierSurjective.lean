module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.CharP.Defs

/-!
# `X ^ p - X` is surjective onto the maximal ideal

This is the core of item **(E9)** of the Kuhlmann decomposition in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppKuhlmannCompleteCase`: the Artin–Schreier normal
form needs that `y ↦ y ^ p - y` hits every element of the maximal ideal of the complete
equal-characteristic ring, so that a `p`-cyclic generator can be normalised to "pole part plus
constant".

## A shorter route than the one the decomposition suggests

The (E9) entry proposes the convergent geometric series `-∑ₖ w ^ (p ^ k)`, which does work —
in characteristic `p`, Frobenius is additive, so that series telescopes:
`y ^ p - y = -∑_{k ≥ 1} w ^ (p ^ k) + ∑_{k ≥ 0} w ^ (p ^ k) = w`.  But formalising it means
setting up summability in the adic topology.

**Hensel's lemma gives it directly and needs no analysis.**  For `w` in the maximal ideal,
`f = X ^ p - X - C w` is monic, its reduction is `X ^ p - X`, and `0` is a root of that
reduction because `w` is in the maximal ideal.  That root is **simple**: in characteristic `p`,
`derivative (X ^ p) = C (p : R) * X ^ (p - 1) = 0`, so `derivative f = -1`, which is a unit.  So
`f` has a root in `R` whenever `R` is henselian.

This is why the statement below needs only `HenselianLocalRing R`, not completeness.  Complete
local rings are henselian — in this tree,
`henselianLocalRing_of_isAdicComplete_maximalIdeal`
— so the complete case Epp works in is covered, but so is any henselian one.

## Main results

* `exists_pow_sub_self_eq_of_mem_maximalIdeal`: for `R` henselian local of characteristic `p`
  prime and `w ∈ 𝔪`, there is `y ∈ R` with `y ^ p - y = w`.
* `pow_sub_self_surjOn_maximalIdeal`: the same, as a surjectivity statement, which is the form
  (E9) consumes.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* Kuhlmann, *A correction to Epp's paper "Elimination of wild ramification"*,
  Invent. Math. **153** (2004) 679–681
-/

@[expose] public section

open Polynomial IsLocalRing

/-- **Artin–Schreier surjectivity onto the maximal ideal.**

If `R` is a henselian local ring of prime characteristic `p` and `w` lies in the maximal ideal,
then `y ^ p - y = w` has a solution in `R`.

The proof is Hensel's lemma applied to `f = X ^ p - X - C w` at the residue `0`: the reduction of
`f` is `X ^ p - X`, which vanishes at `0` precisely because `w ∈ 𝔪`, and
`derivative f = -1` because `derivative (X ^ p) = C (p : R) * X ^ (p - 1)` vanishes in
characteristic `p`.  A simple root lifts, and the lift is the solution. -/
theorem exists_pow_sub_self_eq_of_mem_maximalIdeal {R : Type*} [CommRing R]
    [HenselianLocalRing R] (p : ℕ) (hp : p.Prime) [CharP R p] {w : R}
    (hw : w ∈ maximalIdeal R) :
    ∃ y : R, y ^ p - y = w := by
  classical
  set f : R[X] := X ^ p - (X + C w) with hf
  -- `f` is monic: the subtracted part has degree `1 < p`.
  have hdeg : (X + C w : R[X]).degree < (p : ℕ) := by
    rw [degree_X_add_C]
    exact_mod_cast hp.one_lt
  have hmonic : f.Monic := monic_X_pow_sub hdeg
  -- The residue of `f` vanishes at `0`, and its derivative is the unit `-1`.
  have hres : aeval (0 : ResidueField R) f = 0 := by
    have hwres : residue R w = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hw
    simp [hf, zero_pow hp.ne_zero, hwres]
  have hderiv : aeval (0 : ResidueField R) (derivative f) ≠ 0 := by
    -- `derivative (X ^ p) = C (p : R) * X ^ (p - 1)`, and `simp` discharges `(p : R) = 0`
    -- straight from the `CharP R p` instance, so the characteristic is what kills this term.
    have hd : derivative f = -1 := by simp [hf, derivative_X_pow]
    rw [hd]
    simp
  have htfae := (HenselianLocalRing.TFAE R).out 1 2
  obtain ⟨y, hy, -⟩ := htfae.mp inferInstance f hmonic 0 hres hderiv
  refine ⟨y, ?_⟩
  have hy' := hy
  rw [IsRoot, hf] at hy'
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at hy'
  have hy2 : y ^ p = y + w := sub_eq_zero.mp hy'
  rw [hy2, add_sub_cancel_left]

/-- **(E9)'s surjectivity, in the form the normal form consumes.**

`y ↦ y ^ p - y` maps `R` onto the maximal ideal of a henselian local ring of characteristic `p`.
Restated from `exists_pow_sub_self_eq_of_mem_maximalIdeal` as a `Set.SurjOn`. -/
theorem pow_sub_self_surjOn_maximalIdeal {R : Type*} [CommRing R] [HenselianLocalRing R]
    (p : ℕ) (hp : p.Prime) [CharP R p] :
    ∀ w ∈ (maximalIdeal R : Set R), ∃ y : R, y ^ p - y = w :=
  fun _ hw => exists_pow_sub_self_eq_of_mem_maximalIdeal p hp hw
