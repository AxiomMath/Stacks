module

public import StacksFrontier.RingTheory.LocalCohomology.FinitenessAnnihilatorCriterionPlusConverse

/-!
# Finiteness of the local cohomology of a bounded-below complex, the whole criterion

Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization, let `K` be an
object of `D⁺_{Coh}(A)` — a bounded-below complex every one of whose cohomology modules is
finite — and let `n ∈ ℤ`. The two conditions

1. `H^i_T(K)` is finite for `i ≤ n`,
2. some ideal `J ⊆ A` with `V(J) ⊆ T` annihilates `H^i_T(K)` for `i ≤ n`

are equivalent; and when `T = V(I) = Z` for an ideal `I ⊆ A` they are equivalent in addition to

3. some power `I ^ e` with `e ≥ 0` annihilates `H^i_Z(K)` for `i ≤ n`.

This file states the two equivalences, which is what the three conditions of the source amount
to. Each of their halves is proved elsewhere in the library: the implication from finiteness to
an annihilating ideal in
`StacksFrontier/RingTheory/LocalCohomology/FinitenessAnnihilatorCriterionPlus.lean`, its converse in
`StacksFrontier/RingTheory/LocalCohomology/FinitenessAnnihilatorCriterionPlusConverse.lean`, and the
passage between an arbitrary ideal supported in `V(I)` and a power of `I` in
`StacksFrontier/RingTheory/LocalCohomology/AnnihilatorPowerPlus.lean`. What is new here is the
closed-support equivalence, and in particular the implication `(3) ⟹ (1)`, which goes through
`(3) ⟹ (2) ⟹ (1)`.

## Main results

* `Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_tfae` — the equivalence of the
  source's conditions (1) and (2) for `T` stable under specialization.
* `Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_tfae_zeroLocus` — the
  equivalence of all three for closed support `T = V(I)`.

## Implementation notes

Membership of `K` in `D⁺_{Coh}(A)` is expressed as a bounded-below object together with
finiteness of each of its cohomology modules, as everywhere else in this corner of the library;
the module-level case is Tag 0AW8, whose statement for a finite module `M` is
`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_exists_annihilator`. The
hypothesis that `T` be stable under specialization is used only by the converse; condition (1)
implies condition (2) for an arbitrary subset `T`, as recorded there.

Closed support needs no separate stability hypothesis: a zero locus is closed, hence stable under
specialization.

## References

* [Stacks Project, Tag 0EI1](https://stacks.math.columbia.edu/tag/0EI1)
* [Stacks Project, Tag 0AW8](https://stacks.math.columbia.edu/tag/0AW8)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- **Stacks 0EI1, the equivalence of (1) and (2).** Let `A` be a Noetherian ring, let
`T ⊆ Spec(A)` be stable under specialization, let `K` be an object of `D⁺_{Coh}(A)` and let
`n ∈ ℤ`. Then `H^i_T(K)` is finite for every `i ≤ n` exactly when one ideal `J ⊆ A` with
`V(J) ⊆ T` annihilates `H^i_T(K)` for every `i ≤ n`. -/
@[stacks 0EI1 "the equivalence of (1) and (2), for T stable under specialization and K
bounded below with finite cohomology modules"]
theorem localCohomologyWithSupportInPlus_finite_tfae (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (n : ℤ) :
    List.TFAE
      [∀ i : ℤ, i ≤ n → Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A T K i),
        ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
          ∀ i : ℤ, i ≤ n → J ≤ Module.annihilator A
            (localCohomologyWithSupportInPlus.{u, v} A T K i)] := by
  tfae_have 1 ↔ 2 :=
    localCohomologyWithSupportInPlus_finite_iff_exists_annihilator.{u, v} A T hT K hK n
  tfae_finish

/-- **Stacks 0EI1, the equivalence of (1), (2) and (3) for closed support.** Let `A` be a
Noetherian ring, let `I ⊆ A` be an ideal and write `Z = V(I)`, let `K` be an object of
`D⁺_{Coh}(A)` and let `n ∈ ℤ`. Then the following are equivalent: `H^i_Z(K)` is finite for every
`i ≤ n`; one ideal `J ⊆ A` with `V(J) ⊆ Z` annihilates `H^i_Z(K)` for every `i ≤ n`; some power
`I ^ e` annihilates `H^i_Z(K)` for every `i ≤ n`.

A zero locus is closed, so the first equivalence is the one above, and the second is the
ideal-theoretic statement that an ideal has zero locus inside `V(I)` exactly when it contains a
power of `I`. -/
@[stacks 0EI1 "the equivalence of (1), (2) and (3) for closed support T = V(I), for K
bounded below with finite cohomology modules"]
theorem localCohomologyWithSupportInPlus_finite_tfae_zeroLocus (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (n : ℤ) :
    List.TFAE
      [∀ i : ℤ, i ≤ n → Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A
          (PrimeSpectrum.zeroLocus (I : Set A)) K i),
        ∃ J : Ideal A,
          PrimeSpectrum.zeroLocus (J : Set A) ⊆ PrimeSpectrum.zeroLocus (I : Set A) ∧
          ∀ i : ℤ, i ≤ n → J ≤ Module.annihilator A (localCohomologyWithSupportInPlus.{u, v} A
            (PrimeSpectrum.zeroLocus (I : Set A)) K i),
        ∃ e : ℕ, ∀ i : ℤ, i ≤ n → I ^ e ≤ Module.annihilator A
          (localCohomologyWithSupportInPlus.{u, v} A
            (PrimeSpectrum.zeroLocus (I : Set A)) K i)] := by
  tfae_have 1 ↔ 2 := localCohomologyWithSupportInPlus_finite_iff_exists_annihilator.{u, v} A
    (PrimeSpectrum.zeroLocus (I : Set A))
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization K hK n
  tfae_have 2 ↔ 3 := exists_annihilator_iff_exists_power_annihilator_plus.{u, v} A I K n
  tfae_finish

end Stacks.LocalCohomology

end
