module

public import StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresFinitenessZeroLocus
public import StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresCriterion

/-!
# Finiteness below a degree as a criterion for the cutoff, formal fibres along `V(I)` only

Let `A` be a universally catenary Noetherian ring, `I ⊆ A` an ideal, `Z = V(I)` and `M` a
finite `A`-module. Write `s = s_{A,I}(M)` for the local cohomology finiteness cutoff of Stacks
0BJR. `StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresCriterion` proves that, fixing
`n : ℕ` and assuming the formal fibres of *every* local ring of `A` satisfy Serre's condition
`(Sₙ)`,

`n < s` if and only if `H^i_Z(M)` is a finite `A`-module for every degree `i ≤ n`,

and equivalently for every degree `p + 1` with `p < n`. This file proves the same two
equivalences with the formal-fibres hypothesis imposed only at the primes of `Z`, using the
`V(I)`-restricted finiteness and non-finiteness clauses of
`StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresFinitenessZeroLocus` in place of the
unrestricted ones. The proofs are otherwise identical.

## Main results

* `Stacks.LocalCohomology.lt_localCohomologyCutoff_iff_forall_finiteZeroLocus` — the equivalence
  above, formal fibres only along `V(I)`.
* `Stacks.LocalCohomology.lt_localCohomologyCutoff_iff_forall_finite_succZeroLocus` — the same
  equivalence with the degrees written as `p + 1` for `p < n`.

## Implementation notes

This is the ring-theoretic content of Stacks 0BJY exactly as that tag states its own
formal-fibres hypothesis: "for every `z ∈ Z` the formal fibres of `𝒪_{X,z}` are `(Sₙ)`", not
for every point of `X`.

## References

* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- If `H^s_Z(M)` is finite in every degree `1 ≤ s ≤ n`, then `n < s_{A,I}(M)`. -/
private theorem lt_localCohomologyCutoff_of_forall_finite
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n)
    (h : ∀ s : ℕ, 1 ≤ s → s ≤ n → Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) (s : ℤ))) :
    (n : ℕ∞) < localCohomologyCutoff A I M := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hcon)
  rw [← hs] at hcon
  have hsn : s ≤ n := by exact_mod_cast hcon
  have hs1 : 1 ≤ s := by
    have h1 := one_le_localCohomologyCutoff A I M
    rw [← hs] at h1
    exact_mod_cast h1
  exact not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibersZeroLocus
    A I M hA s (fun p hp => (hformal p hp).mono (by omega)) hs.symm (h s hs1 hsn)

/-- **The cutoff criterion for finiteness of local cohomology, formal fibres only along
`V(I)`.** Let `A` be a universally catenary Noetherian ring, `I ⊆ A` an ideal, `Z = V(I)` and
`M` a finite `A`-module. If the formal fibres of `𝒪_{Spec A, z}` satisfy Serre's condition
`(Sₙ)` for every `z ∈ Z`, then the cutoff `s = s_{A,I}(M)` of Stacks 0BJR exceeds `n` exactly
when `H^i_Z(M)` is a finite `A`-module in every degree `i ≤ n`.

Forwards this is
`finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibersZeroLocus`.
Backwards, if `s ≤ n` then `s` is a natural number, the formal fibres along `V(I)` satisfy
`(S_{s-1})` because `s - 1 ≤ n`, and
`not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibersZeroLocus`
makes `H^s_Z(M)` infinite in a degree `s ≤ n`. -/
public theorem lt_localCohomologyCutoff_iff_forall_finiteZeroLocus
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n) :
    (n : ℕ∞) < localCohomologyCutoff A I M ↔
      ∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
  refine ⟨fun hn =>
    finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibersZeroLocus
      A I M hA n hformal hn, fun h =>
    lt_localCohomologyCutoff_of_forall_finite A I M hA n hformal fun s _ hsn =>
      h (s : ℤ) (by exact_mod_cast hsn)⟩

/-- **The cutoff criterion in the degrees Stacks 0BK0 produces, formal fibres only along
`V(I)`.** In the situation of `lt_localCohomologyCutoff_iff_forall_finiteZeroLocus`, the cutoff
exceeds `n` exactly when `H^{p+1}_Z(M)` is a finite `A`-module for every `p < n`. -/
public theorem lt_localCohomologyCutoff_iff_forall_finite_succZeroLocus
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n) :
    (n : ℕ∞) < localCohomologyCutoff A I M ↔
      ∀ p : ℕ, p < n → Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))
          ((p + 1 : ℕ) : ℤ)) := by
  refine ⟨fun hn p hp =>
    (lt_localCohomologyCutoff_iff_forall_finiteZeroLocus A I M hA n hformal).mp hn
      ((p + 1 : ℕ) : ℤ) (by exact_mod_cast hp), fun h =>
    lt_localCohomologyCutoff_of_forall_finite A I M hA n hformal fun s hs1 hsn => ?_⟩
  have hfin := h (s - 1) (by omega)
  rwa [show ((s - 1 + 1 : ℕ) : ℤ) = (s : ℤ) by omega] at hfin

end Stacks.LocalCohomology

end
