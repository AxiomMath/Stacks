module

public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessAnnihilatorCriterion

/-!
# Finiteness of local cohomology and the depth-dimension inequality

Let `A` be a Noetherian ring admitting a dualizing complex, let `T ⊆ Spec(A)` be stable under
specialization, let `M` be a finite `A`-module and let `s ≥ 0`. The local cohomology modules
`H^i_T(M)` are finite for `i ≤ s` exactly when
`depth_{A_p}(M_p) + dim((A/p)_q) > s` for every pair of primes `p ⊆ q` with `p ∉ T` and `q ∈ T`.

## Main results

* `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_depth_add_dim` —
  **Stacks 0EFD**, Faltings' finiteness criterion.

## References

* [Faltings, *Über die Annulatoren lokaler Kohomologiegruppen*][Faltings-annulators]
* [Stacks Project, Proposition 51.11.1 (0EFD)](https://stacks.math.columbia.edu/tag/0EFD)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (enatToEInt krullDimToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-! ### Comparing depths and dimensions with a natural-number bound -/

/-- A prime lies in the zero locus of `I` exactly when it contains `I`. -/
public theorem mem_zeroLocus_iff {A : Type u} [CommRing A] (I : Ideal A) (x : PrimeSpectrum A) :
    x ∈ PrimeSpectrum.zeroLocus (I : Set A) ↔ I ≤ x.asIdeal := by
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]

/-- For `n : ℕ` and `d h : ℕ∞`, the inequality `n < d + h` holds in `ℕ∞` exactly when it holds
after `d` and `h` are cast to `EInt` by `enatToEInt` and `krullDimToEInt`. -/
public theorem natCast_lt_add_iff_eint (n : ℕ) (d h : ℕ∞) :
    (n : ℕ∞) < d + h ↔
      enatToEInt d + krullDimToEInt (h : WithBot ℕ∞) > ((n : ℤ) : EInt) := by
  cases d <;> cases h
  case coe.coe d h =>
    dsimp [enatToEInt, krullDimToEInt, WithBotTop.coe]
    change (n : ℕ∞) < d + h ↔ ((d + h : ℤ) : EInt) > ((n : ℤ) : EInt)
    simp only [WithBotTop.coe_lt_coe]
    norm_cast
  all_goals exact ⟨fun _ ↦ show ((n : ℤ) : EInt) < ⊤ from eint_natCast_lt_top n, fun _ ↦ by simp⟩

/-- **Faltings' finiteness criterion.** For a finite module `M` over a Noetherian ring `A` with a
dualizing complex and a specialization-stable `T ⊆ Spec(A)`, the local cohomology modules
`H^i_T(M)` are finite for `i ≤ s` if and only if
`depth_{A_p}(M_p) + dim((A/p)_q) > s` whenever `p ⊆ q` with `p ∉ T` and `q ∈ T`. -/
@[stacks 0EFD]
public theorem finite_localCohomologyWithSupportIn_iff_depth_add_dim
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) (s : ℕ)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega)) :
    (∀ i : ℤ, i ≤ (s : ℤ) → Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i)) ↔
      (∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → p.asIdeal ≤ q.asIdeal →
        enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
          krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > ((s : ℤ) : EInt)) :=
  (finite_localCohomologyWithSupportIn_iff_exists_annihilator.{u, u} A T hT
      (ModuleCat.of A M) s).trans
    (exists_ideal_le_annihilator_localCohomology_iff A M T T Set.Subset.rfl hT hT
      (s : ℤ) (Int.natCast_nonneg s) omega homega)

end Stacks.LocalCohomology
