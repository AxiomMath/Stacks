module

public import StacksFrontier.RingTheory.F6Rank301.AnnihilatingLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessAnnihilatorCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of local cohomology of generically locally free modules

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `Z = V(I)` and `n ≥ 0`. If the local cohomology
modules `H^i_Z(A)` of the ring itself are finite for `0 ≤ i ≤ n`, then so are the modules
`H^i_Z(M)` for every finite `A`-module `M` whose localization `M_f` is a finite locally free
`A_f`-module for every `f ∈ I`.

The proof is the composition of three results. Finiteness of `H^i_Z(A)` through degree `n` is
equivalent, by the annihilator criterion
`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_exists_pow_annihilator`, to the
existence of a single power `I ^ e` annihilating all of them. That power-torsion statement
transfers from `A` to `M` by
`Stacks.LocalCohomology.exists_pow_smul_localCohomology_eq_bot`, which is exactly where the
hypothesis on the localizations of `M` is used. Applying the annihilator criterion to `M` in the
other direction returns finiteness.

## Main results

* `Stacks.LocalCohomology.localCohomologyWithSupportIn_finite_of_finiteLocallyFree_away` —
  **Stacks 0BPY.**

## Implementation notes

The powers produced by the transfer step depend on the degree, so they are collected into a single
exponent by taking the supremum over the finitely many degrees `0 ≤ i ≤ n`; in negative degrees
the local cohomology vanishes and the annihilator is the unit ideal, so the criterion's hypothesis
over all integers `i ≤ n` follows from the hypothesis over the natural numbers `i ≤ n`.

Local cohomology is `Stacks.LocalCohomology.localCohomologyWithSupportIn`, the set-indexed model,
applied to the module placed in degree zero; the subset is the closed set
`PrimeSpectrum.zeroLocus I`.

## References

* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
* [Stacks Project, Tag 0BPX](https://stacks.math.columbia.edu/tag/0BPX)
* [Stacks Project, Tag 0AW8](https://stacks.math.columbia.edu/tag/0AW8)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- Finiteness of local cohomology with support in a closed set, in all integral degrees at most
`n`, follows from finiteness in the natural-number degrees at most `n`: the modules in negative
degrees vanish. -/
private lemma finite_localCohomology_int_of_nat (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)]
    (h : ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ))) :
    ∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i) := by
  intro i hi
  rcases lt_or_ge i 0 with hneg | hpos
  · exact finite_localCohomologyWithSupportIn_of_nonpos.{u, 0} A _ M i hneg.le
  · lift i to ℕ using hpos
    exact h i (by omega)

/-- **Stacks 0BPY.** Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `Z = V(I)` and `n ≥ 0`. If
the local cohomology `H^i_Z(A)` of the ring is finite for `0 ≤ i ≤ n`, then `H^i_Z(M)` is finite
for `0 ≤ i ≤ n`, for every finite `A`-module `M` such that `M_f` is a finite locally free
`A_f`-module for every `f ∈ I`.

Finiteness for `A` through degree `n` produces a power `I ^ e` annihilating `H^i_Z(A)` for
`i ≤ n`; that power-torsion property transfers to `M`, degree by degree, and the exponents are
collected into a single one; the annihilator criterion then returns finiteness for `M`. -/
@[stacks 0BPY]
theorem localCohomologyWithSupportIn_finite_of_finiteLocallyFree_away
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ)
    (hA : ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyWithSupportIn.{u, 0} A
        (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) (i : ℤ)))
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)]
    (hM : ∀ f ∈ I, Module.IsFiniteLocallyFree (Localization.Away f)
      (LocalizedModule.Away f (M : Type u))) :
    ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyWithSupportIn.{u, 0} A
        (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ)) := by
  obtain ⟨e, he⟩ :=
    (finite_localCohomologyWithSupportIn_iff_exists_pow_annihilator.{u, 0} A I
      (ModuleCat.of A A) n).mp
      (finite_localCohomology_int_of_nat A I n (ModuleCat.of A A) hA)
  have hFP : Module.FinitePresentation A (M : Type u) :=
    Module.finitePresentation_of_finite A (M : Type u)
  have key : ∀ i : ℕ, ∃ m : ℕ, i ≤ n → I ^ m ≤ Module.annihilator A
      (localCohomologyWithSupportIn.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ)) := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨m, hm⟩ := exists_pow_smul_localCohomology_eq_bot A I I le_rfl
        (Ideal.fg_of_isNoetherianRing I) i
        ⟨e, Submodule.le_annihilator_iff.mp
          (by rw [Submodule.annihilator_top]; exact he (i : ℤ) (by exact_mod_cast hi))⟩
        M hFP hM
      refine ⟨m, fun _ ↦ ?_⟩
      rw [← Submodule.annihilator_top]
      exact Submodule.le_annihilator_iff.mpr hm
    · exact ⟨0, fun h ↦ absurd h hi⟩
  choose m hm using key
  intro i hi
  refine (finite_localCohomologyWithSupportIn_iff_exists_pow_annihilator.{u, 0} A I M n).mpr
    ⟨(Finset.range (n + 1)).sup m, ?_⟩ (i : ℤ) (by exact_mod_cast hi)
  intro j hj
  rcases lt_or_ge j 0 with hneg | hpos
  · rw [Module.annihilator_eq_top_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_localCohomologyWithSupportIn_of_neg.{u, 0} _ M j hneg))]
    exact le_top
  · lift j to ℕ using hpos
    refine (Ideal.pow_le_pow_right ?_).trans (hm j (by omega))
    exact Finset.le_sup (Finset.mem_range.mpr (by omega))

end Stacks.LocalCohomology

end
