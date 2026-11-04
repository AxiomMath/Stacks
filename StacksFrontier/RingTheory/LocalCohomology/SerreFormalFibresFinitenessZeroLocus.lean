module

public import StacksFrontier.RingTheory.LocalCohomology.Cutoff.AttainmentZeroLocus
public import StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresFiniteness

/-!
# Finiteness of local cohomology under a Serre condition imposed along `V(I)` only

Let `A` be a universally catenary Noetherian ring, `I ⊆ A` an ideal, `Z = V(I) ⊆ Spec(A)` and
`M` a finite `A`-module. Write `s = s_{A,I}(M)` for the local cohomology finiteness cutoff of
Stacks 0BJR. The two conclusions of Stacks 0BJW hold with Serre's condition on the formal
fibres imposed only at the primes of `Z`, rather than at every prime of `A`: `H^i_Z(M)` is finite
for `i ≤ n` when `n < s` and the formal fibres along `Z` satisfy `(S_n)`, and `H^s_Z(M)` is not
finite when `s` is finite and the formal fibres along `Z` satisfy `(S_{s-1})`.

## Main results

In the namespace `Stacks.LocalCohomology`:

* `finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibersZeroLocus`:
  finiteness through a degree `n` below the cutoff, formal fibres `(S_n)` only along `V(I)`.
* `not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibersZeroLocus`:
  non-finiteness in the cutoff degree, formal fibres `(S_{s-1})` only along `V(I)`.

## References

* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The finiteness clause, formal fibres `(S_n)` only along `V(I)`. -/
private theorem
    finite_localCohomologyModule_of_lt_localCohomologyCutoff_of_serreFormalFibersZeroLocus
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n)
    (hn : (n : ℕ∞) < localCohomologyCutoff A I M) :
    ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) (ModuleCat.of A M) (i : ℤ)) := by
  rw [finite_localCohomologyModule_iff_forall_completedLocalization]
  intro p i hi
  have hcut := lt_localCohomologyCutoff_adicCompletion_localization_zeroLocus A I M n hA
    hformal hn p
  rw [Ideal.map_map] at hcut
  exact (finite_localCohomologyModule_completedLocalRingAt_iff A I
    (Ideal.fg_of_isNoetherianRing I) M p n).mpr hcut i hi

/-- **Finiteness through a degree below the cutoff, formal fibres `(S_n)` only along `V(I)`.**
Let `A` be a universally catenary Noetherian ring, `I ⊆ A` an ideal, `Z = V(I)` and `M` a finite
`A`-module. Fix a natural number `n` strictly below the cutoff `s = s_{A,I}(M)` of Stacks 0BJR
and assume only that the formal fibres of `𝒪_{Spec A, z}` satisfy Serre's condition `(S_n)` for
every `z ∈ Z`. Then `H^i_Z(M)` is a finite `A`-module in every degree `i ≤ n`. -/
public theorem
    finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibersZeroLocus
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n)
    (hn : (n : ℕ∞) < localCohomologyCutoff A I M) (i : ℤ) (hi : i ≤ (n : ℤ)) :
    Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) :=
  (finite_forall_int_iff_forall_nat A I (Ideal.fg_of_isNoetherianRing I)
      (ModuleCat.of A M) n).mpr
    (finite_localCohomologyModule_of_lt_localCohomologyCutoff_of_serreFormalFibersZeroLocus A I M
      hA n hformal hn) i hi

/-- **Non-finiteness at the cutoff, formal fibres `(S_{s-1})` only along `V(I)`.** In the
situation of
`finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibersZeroLocus`,
if the cutoff `s = s_{A,I}(M)` is the natural number `s` and the formal fibres of `𝒪_{Spec A,z}`
satisfy Serre's condition `(S_{s-1})` for every `z ∈ V(I)`, then `H^s_Z(M)` is *not* a finite
`A`-module. -/
public theorem
    not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibersZeroLocus
    (hA : Ring.IsUniversallyCatenary A) (s : ℕ)
    (hformal : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) (s - 1))
    (hs : localCohomologyCutoff A I M = (s : ℕ∞)) :
    ¬ Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))
        (s : ℤ)) := by
  intro hfin
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  have hfin' : Module.Finite A (localCohomologyModule A I hI (ModuleCat.of A M) (s : ℤ)) :=
    Module.Finite.equiv
      (localCohomologyWithSupportInIsoLocalCohomologyModule A I hI
        (ModuleCat.of A M) (s : ℤ)).toLinearEquiv
  have hall : ∀ i : ℕ, i ≤ s →
      Module.Finite A (localCohomologyModule A I hI (ModuleCat.of A M) (i : ℤ)) := by
    intro i hi
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact hfin'
    · refine finite_localCohomologyModule_of_lt_localCohomologyCutoff_of_serreFormalFibersZeroLocus
        A I M hA (s - 1) hformal ?_ i (by omega)
      rw [hs]
      exact_mod_cast Nat.sub_lt (by omega) Nat.one_pos
  have hfa := (finite_localCohomologyModule_iff_forall_completedLocalization A I hI M s).mp hall
  obtain ⟨q, _, hcut⟩ :=
    exists_localCohomologyCutoff_adicCompletion_localization_eq_zeroLocus A I M hA
      (by rw [hs]; exact ENat.natCast_lt_top s) (by rwa [hs, ENat.toNat_natCast])
  rw [Ideal.map_map, hs] at hcut
  have hlt := (finite_localCohomologyModule_completedLocalRingAt_iff A I hI M q s).mp (hfa q)
  rw [hcut] at hlt
  exact lt_irrefl _ hlt

end Stacks.LocalCohomology

end
