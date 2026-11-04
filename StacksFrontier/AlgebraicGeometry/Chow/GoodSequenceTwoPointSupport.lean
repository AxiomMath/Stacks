module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Support
public import StacksFrontier.AlgebraicGeometry.Chow.LengthsDeterminants.GoodSequences
public import StacksFrontier.RingTheory.Support.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Sequences with prime successive quotients for a module supported at two points

Let `R` be a Noetherian local ring and `q` a prime of `R`. A finite `R`-module whose support
consists of at most the closed point and `q` admits a sequence whose successive quotients are
copies of `R / q` and whose span removes `q` from the support, with no minimality hypothesis
on `q`: either `q` lies in the support, where it is automatically minimal, or the empty
sequence works.

Over such a ring, a finite-length module is annihilated by an element outside any prime other
than the maximal ideal.

## Main results

* `Module.FiniteLength.exists_sequence_with_successive_quotients_of_support_subset` produces the
  sequence.
* `Module.FiniteLength.minimal_support_of_support_subset` is the minimality that makes
  Tag 02QC applicable.
* `Module.FiniteLength.exists_notMem_smul_eq_zero_of_isFiniteLength` produces the annihilating
  element outside the prime.

## Implementation notes

The support is `Module.support`, a set of points of the prime spectrum ordered by inclusion of
the corresponding ideals, so minimality in the support is minimality for that order. The
sequence is presented as in Tag 02QC, by the successive subquotients of the spans of its
initial segments.

## References

* [Stacks Project, Tag 02QC](https://stacks.math.columbia.edu/tag/02QC)
* [Stacks Project, Tag 00L6](https://stacks.math.columbia.edu/tag/00L6)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v

/-- A prime in the support of a module whose support meets no prime other than it and the
closed point is minimal in that support. -/
public theorem minimal_support_of_support_subset
    {R : Type u} {N : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] (q : PrimeSpectrum R)
    (hsupp : Module.support R N ⊆ {IsLocalRing.closedPoint R, q})
    (hq : q ∈ Module.support R N) :
    Minimal (· ∈ Module.support R N) q := by
  refine ⟨hq, fun p hp _ ↦ ?_⟩
  have hp' := hsupp hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
  rcases hp' with rfl | rfl
  · exact IsLocalRing.le_maximalIdeal q.isPrime.ne_top
  · exact le_rfl

/-- **Stacks Project, Tag 02QC.** A finite module whose support meets no prime other than `q`
and the closed point admits a sequence whose successive quotients are copies of `R / q` and
whose span removes `q` from the support. Its number of terms is the localized length at `q`. -/
@[stacks 02QC "support at two points"]
public theorem exists_sequence_with_successive_quotients_of_support_subset
    {R : Type u} {N : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (q : PrimeSpectrum R)
    (hsupp : Module.support R N ⊆ {IsLocalRing.closedPoint R, q}) :
    ∃ (l : ℕ) (x : Fin l → N),
      q ∉ Module.support R (N ⧸ Submodule.span R (Set.range x)) ∧
      (∀ i : Fin l,
        Nonempty
          (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R N) ⧸
              (spanBefore (R := R) x i).comap
                (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R N).subtype) ≃ₗ[R]
            R ⧸ q.asIdeal)) ∧
      l = (Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl N)).toNat := by
  by_cases hq : q ∈ Module.support R N
  · exact exists_sequence_with_successive_quotients_at_minimal_support q
      (minimal_support_of_support_subset q hsupp hq)
  · have hbot : Submodule.span R (Set.range (Fin.elim0 : Fin 0 → N)) = ⊥ := by simp
    refine ⟨0, Fin.elim0, ?_, fun i ↦ i.elim0, ?_⟩
    · have e : (N ⧸ Submodule.span R (Set.range (Fin.elim0 : Fin 0 → N))) ≃ₗ[R] N :=
        (Submodule.quotEquivOfEq _ ⊥ hbot).trans ((⊥ : Submodule R N).quotEquivOfEqBot rfl)
      rw [LinearEquiv.support_eq e]
      exact hq
    · have hsub : Subsingleton (LocalizedModule q.asIdeal.primeCompl N) :=
        Module.notMem_support_iff.mp hq
      rw [Module.length_eq_zero_iff.mpr hsub]
      rfl

/-- A finite module of finite length over a Noetherian local ring is annihilated by some
element lying outside any given prime other than the maximal ideal. -/
public theorem exists_notMem_smul_eq_zero_of_isFiniteLength
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : IsFiniteLength R M)
    (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R) :
    ∃ d : R, d ∉ q ∧ ∀ m : M, d • m = 0 := by
  have hsupp : Module.support R M
      ⊆ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R) := by
    rw [zeroLocus_maximalIdeal]
    rcases subsingleton_or_nontrivial M with h | h
    · rw [Module.support_eq_empty_iff.mpr h]
      exact Set.empty_subset _
    · exact (support_of_isFiniteLength hM).le
  obtain ⟨n, hn⟩ := (main_theorem_00l6 (IsLocalRing.maximalIdeal R)).mpr hsupp
  have hsucc : (IsLocalRing.maximalIdeal R ^ (n + 1)) • (⊤ : Submodule R M) = ⊥ :=
    le_bot_iff.mp (hn.le.trans' (Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)))
  have hnotle : ¬ IsLocalRing.maximalIdeal R ^ (n + 1) ≤ q := by
    intro hle
    exact hq (le_antisymm (IsLocalRing.le_maximalIdeal ‹q.IsPrime›.ne_top)
      fun a ha ↦ ‹q.IsPrime›.mem_of_pow_mem (n + 1) (hle (Ideal.pow_mem_pow ha (n + 1))))
  obtain ⟨d, hdm, hdq⟩ := Set.not_subset.mp hnotle
  refine ⟨d, hdq, fun m ↦ ?_⟩
  have hmem : d • m ∈ (IsLocalRing.maximalIdeal R ^ (n + 1)) • (⊤ : Submodule R M) :=
    Submodule.smul_mem_smul hdm Submodule.mem_top
  rw [hsucc] at hmem
  simpa using hmem

end Module.FiniteLength
