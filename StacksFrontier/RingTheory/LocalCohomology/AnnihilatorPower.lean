module

public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport

/-!
# Annihilating local cohomology with closed support by a power of the ideal

Let `A` be a Noetherian ring and `I ⊆ A` an ideal, and write `Z = V(I)` for its zero locus.
For an object `K` of the derived category of `A`-modules, the local cohomology modules
`H^i_Z(K)` are annihilated by some ideal `J` whose zero locus is contained in `Z`, uniformly
for `i ≤ n`, exactly when they are annihilated by a single power `I^e`. This is the
implication `(2) ⇔ (3)` of Tag 0AW8, which the source leaves to the reader; unlike the
equivalence with finiteness it is pure ideal theory, requires no hypothesis on the module, and
is here proved in the generality of an arbitrary family of ideals.

The two ingredients are that `V(J) ⊆ V(I)` says exactly `I ≤ √J`, so that a finitely generated
`I` has a power inside `J`, and conversely that `V(I^e) = V(I)` for `e ≥ 1`.

## Main results

* `Stacks.LocalCohomology.exists_le_iff_exists_pow_le` — the ideal-theoretic statement, for an
  arbitrary family of ideals indexed by the degree.
* `Stacks.LocalCohomology.exists_annihilator_iff_exists_power_annihilator` — its specialisation
  to the annihilators of local cohomology with support in `V(I)`.

## References

* [Faltings, *Über die Annullatoren lokaler Kohomologiegruppen*][Faltings-annulators]
* [Stacks Project, Tag 0AW8](https://stacks.math.columbia.edu/tag/0AW8)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- Let `I` be an ideal of a Noetherian ring `A` and let `a : ℤ → Ideal A` be any family of
ideals. There is an ideal `J` with `V(J) ⊆ V(I)` contained in `a i` for all `i ≤ n` if and only
if some power `I ^ e` is contained in `a i` for all `i ≤ n`.

Forward: `V(J) ⊆ V(I)` means `I ≤ √J`, and `I` is finitely generated, so `I ^ e ≤ J` for some
`e`. Backward: `J := I ^ (e + 1)` has `V(J) = V(I)` and is contained in `I ^ e`. -/
theorem exists_le_iff_exists_pow_le (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℤ) (a : ℤ → Ideal A) :
    (∃ J : Ideal A,
      PrimeSpectrum.zeroLocus (J : Set A) ⊆ PrimeSpectrum.zeroLocus (I : Set A) ∧
        ∀ i : ℤ, i ≤ n → J ≤ a i) ↔
      (∃ e : ℕ, ∀ i : ℤ, i ≤ n → I ^ e ≤ a i) := by
  constructor
  · rintro ⟨J, hJ, hle⟩
    rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hJ
    obtain ⟨e, he⟩ :=
      Ideal.exists_pow_le_of_le_radical_of_fg hJ (Ideal.fg_of_isNoetherianRing I)
    exact ⟨e, fun i hi ↦ he.trans (hle i hi)⟩
  · rintro ⟨e, he⟩
    exact ⟨I ^ (e + 1), (PrimeSpectrum.zeroLocus_pow I (Nat.succ_ne_zero e)).le,
      fun i hi ↦ (Ideal.pow_le_pow_right (Nat.le_succ e)).trans (he i hi)⟩

/-- **Stacks 0AW8, equivalence of (2) and (3) for closed support.** For support `V(I)` in a
Noetherian ring, an ideal supported in `V(I)` annihilates local cohomology through degree `n`
exactly when a single power of `I` does so. -/
@[stacks 0AW8 "equivalence of (2) and (3) for closed support"]
theorem exists_annihilator_iff_exists_power_annihilator
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{max u v} A) (n : ℕ) :
    (∃ J : Ideal A,
      PrimeSpectrum.zeroLocus (J : Set A) ⊆ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ i : ℤ, i ≤ (n : ℤ) → J ≤ Module.annihilator A
        (localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ↔
      (∃ e : ℕ, ∀ i : ℤ, i ≤ (n : ℤ) → I ^ e ≤ Module.annihilator A
        (localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) :=
  exists_le_iff_exists_pow_le A I n fun i ↦ Module.annihilator A
    (localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)

end Stacks.LocalCohomology
