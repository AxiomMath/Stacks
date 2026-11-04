module

public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksFrontier.RingTheory.KrullDimension.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quotienting by an ideal that avoids every minimal prime drops the dimension

Let `R` be a Noetherian ring and `I` an ideal of `R` contained in no minimal prime of `R`. Then

`dim (R ⧸ I) + 1 ≤ dim R`.

Prime avoidance supplies an element `a ∈ I` outside every minimal prime — there are finitely
many of them, so `I` is not covered by their union — and such an element is a nonzerodivisor on
`R` in the sense needed for `Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes`,
which gives `dim (R ⧸ (a)) + 1 ≤ dim R`. Since `(a) ≤ I` the quotient by `I` is a quotient of
`R ⧸ (a)`, so its dimension is no larger.

## Main definitions

No new definitions are introduced.

## Main results

* `ringKrullDim_quotient_succ_le_of_forall_notMem_minimalPrimes`: the inequality above.

## Implementation notes

Krull dimensions take values in `WithBot ℕ∞`; the statement is additive, so no truncated
subtraction appears. The hypothesis is phrased as `¬ I ≤ p` for every minimal prime `p` of the
zero ideal, which is the form in which it arises: an ideal all of whose generators are
nonzerodivisors satisfies it.
-/

@[expose] public section

universe u

/-- **Quotienting by an ideal avoiding every minimal prime drops the dimension.** For `R`
Noetherian and `I` an ideal contained in no minimal prime of `R`, the quotient `R ⧸ I` has Krull
dimension at least one less than that of `R`. -/
@[ega "0 16.1.2" "Noetherian rings"]
theorem ringKrullDim_quotient_succ_le_of_forall_notMem_minimalPrimes {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, ¬ I ≤ p) :
    ringKrullDim (R ⧸ I) + 1 ≤ ringKrullDim R := by
  have hnot : ¬ ((I : Set R) ⊆ ⋃ p ∈ (⊥ : Ideal R).minimalPrimes, (p : Set R)) := by
    intro hsub
    obtain ⟨p, hp, hIp⟩ := (Ideal.subset_union_prime_finite
      (Ideal.finite_minimalPrimes_of_isNoetherianRing R (⊥ : Ideal R))
      (a := (⊤ : Ideal R)) (b := ⊤) (f := id)
      (fun p hp _ _ => hp.1.1)).mp hsub
    exact hI p hp hIp
  obtain ⟨a, haI, haNot⟩ := Set.not_subset.mp hnot
  have haavoid : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, a ∉ p := by simpa using haNot
  have hdropA : ringKrullDim (R ⧸ Ideal.span {a}) + 1 ≤ ringKrullDim R := by
    have havoid : ∀ p ∈ (Module.annihilator R R).minimalPrimes, a ∉ p := by
      simpa only [Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul R R)] using haavoid
    have h := Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
      (R := R) (M := R) (x := a) havoid
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, Submodule.annihilator_quotient,
      Submodule.colon_univ, Module.supportDim_self_eq_ringKrullDim] at h
    rwa [← Submodule.ideal_span_singleton_smul a (⊤ : Submodule R R), Ideal.smul_top_eq_map,
      Algebra.algebraMap_self, Ideal.map_id, Submodule.restrictScalars_self] at h
  grw [ringKrullDim_le_of_surjective _
    (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem I).mpr haI))]
  exact hdropA

end
