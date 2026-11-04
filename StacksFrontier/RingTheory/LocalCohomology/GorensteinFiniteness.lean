module

public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.LocalCohomology.BoundedBelow
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCutoff
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessDepthDimension

/-!
# Finiteness of local cohomology over a Gorenstein local ring

Let `A` be a Gorenstein Noetherian local ring, let `I ⊆ A` be an ideal, let `Z = V(I)` and let
`M` be a finite `A`-module. Write `s = s_{A,I}(M)` for the local cohomology finiteness cutoff of
Tag 0BJR, which is `Stacks.LocalCohomology.localCohomologyCutoff A I M`. Then `H^i_Z(M)` is a
finite `A`-module for every `i < s`, while `H^s_Z(M)` is not finite.

A Noetherian local ring is Gorenstein exactly when `A[0]` is a dualizing complex for `A`, which
is how `Dualizing.IsGorensteinLocalRing` is defined. So the hypothesis of this tag *is* a
dualizing complex, and the statement is the specialization of Faltings' finiteness criterion
`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_depth_add_dim` (Tag 0EFD) to
`T = V(I)` and `omega = A[0]`, after the two numerical translations described below.

## Main results

* `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff` —
  for a Gorenstein local ring, `H^i_{V(I)}(M)` is finite for all `i ≤ n` exactly when
  `n < s_{A,I}(M)`. This is Tag 0EFD rewritten in terms of the cutoff of Tag 0BJR.
* `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff` — the
  first half of Tag 0BJU: finiteness strictly below the cutoff.
* `Stacks.LocalCohomology.not_finite_localCohomologyWithSupportIn_localCohomologyCutoff` — the
  second half of Tag 0BJU: non-finiteness at a finite cutoff.
* `Stacks.LocalCohomology.finite_lt_and_not_finite_localCohomologyCutoff` — **Tag 0BJU**, both
  halves together.

## Implementation notes

Tag 0EFD is stated with the degree bound `i ≤ n` for a natural number `n` and with the
depth-plus-dimension inequality read in `EInt`, with the dimension of `(A/𝔭)_𝔮` spelled as
`ringKrullDim (A_𝔮 ⧸ 𝔭A_𝔮)`. Tag 0BJR is stated in `ℕ∞` with that dimension spelled as the
height of the image of `𝔮` in `A/𝔭`. Two lemmas reconcile them:
`natCast_lt_add_iff_eint` moves the inequality between `ℕ∞` and `EInt`, and
`ringKrullDim_localization_quotient_eq_height` identifies the two spellings of the dimension,
through `ringKrullDim_quotient_map_ker_eq_height`. With those in hand the clause of Tag 0EFD
becomes `n + 1 ≤ s_{A,I}(M)`, i.e. `n < s_{A,I}(M)`, by
`Stacks.LocalCohomology.le_localCohomologyCutoff_iff`.

The cutoff is an `sInf` in `ℕ∞`, so it is `⊤` exactly when no admissible pair of primes exists.
The two halves are therefore stated so as to stay correct in that degenerate case: the first
half is indexed by a natural number `n` strictly below the cutoff, which for `s = ⊤` means every
`n` and hence finiteness in every degree; and the second half is hypothesized on
`localCohomologyCutoff A I M = (s : ℕ∞)` for a natural number `s`, which is vacuous when the
cutoff is `⊤`. There is no degree `⊤`, so this is exactly the content of the source statement.

The non-finiteness half is deduced from the finiteness half: if `H^s_{V(I)}(M)` were finite then,
together with finiteness in all degrees `< s`, Tag 0EFD would give `s < s`. Finiteness in the
degrees `i < s` is the first half when `s > 0`, and for `s = 0` it is the vanishing of local
cohomology in negative degrees,
`Stacks.LocalCohomology.subsingleton_localCohomologyWithSupportIn_single_of_neg`.

## References

* [Faltings, *Über die Annulatoren lokaler Kohomologiegruppen*][Faltings-annulators], Satz 1
* [Stacks Project, Tag 0BJU](https://stacks.math.columbia.edu/tag/0BJU)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0DW7](https://stacks.math.columbia.edu/tag/0DW7)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **Tag 0EFD for a Gorenstein local ring, in terms of the cutoff of Tag 0BJR.**

For a finite module `M` over a Gorenstein Noetherian local ring `A` and an ideal `I`, the local
cohomology modules `H^i_{V(I)}(M)` are finite for every `i ≤ n` if and only if
`n < s_{A,I}(M)`.

Gorensteinness is exactly the statement that `A[0]` is a dualizing complex, so Faltings'
criterion applies with `omega = A[0]`; the depth-plus-dimension clause it produces is turned
into the inequality `n < s_{A,I}(M)` by `le_localCohomologyCutoff_iff`. -/
public theorem finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Dualizing.IsGorensteinLocalRing A) (I : Ideal A) (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i)) ↔
      (n : ℕ∞) < localCohomologyCutoff A I M := by
  have hT : StableUnderSpecialization (PrimeSpectrum.zeroLocus (I : Set A)) :=
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  rw [finite_localCohomologyWithSupportIn_iff_depth_add_dim A
      (PrimeSpectrum.zeroLocus (I : Set A)) hT n M
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) hA,
    ← ENat.add_one_le_iff (ENat.natCast_ne_top n), le_localCohomologyCutoff_iff]
  refine forall₂_congr fun p q => ?_
  rw [mem_zeroLocus_iff, mem_zeroLocus_iff]
  refine imp_congr_right fun hp => imp_congr_right fun hq => imp_congr_right fun hpq => ?_
  rw [ringKrullDim_localization_quotient_eq_height p q hpq, ← natCast_lt_add_iff_eint,
    ENat.add_one_le_iff (ENat.natCast_ne_top n)]

/-- **The first half of Tag 0BJU.** Over a Gorenstein Noetherian local ring, the local
cohomology modules `H^i_{V(I)}(M)` of a finite module are finite in every degree `i ≤ n` with
`n` strictly below the cutoff `s_{A,I}(M)`. If the cutoff is `⊤` this gives finiteness in every
degree. -/
public theorem finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Dualizing.IsGorensteinLocalRing A) (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ)
    (hn : (n : ℕ∞) < localCohomologyCutoff A I M) (i : ℤ) (hi : i ≤ (n : ℤ)) :
    Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) :=
  (finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff A hA I n M).mpr hn i hi

/-- **The second half of Tag 0BJU.** Over a Gorenstein Noetherian local ring, if the cutoff
`s_{A,I}(M)` is the natural number `s`, then `H^s_{V(I)}(M)` is *not* a finite `A`-module.

Were it finite, it would join the finite modules in the degrees below `s` to make `H^i_{V(I)}(M)`
finite for all `i ≤ s`, and Tag 0EFD would then force `s < s`. -/
public theorem not_finite_localCohomologyWithSupportIn_localCohomologyCutoff
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Dualizing.IsGorensteinLocalRing A) (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (s : ℕ)
    (hs : localCohomologyCutoff A I M = (s : ℕ∞)) :
    ¬ Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) (s : ℤ)) := by
  intro hfin
  have hall : ∀ i : ℤ, i ≤ (s : ℤ) → Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
    intro i hi
    rcases eq_or_lt_of_le hi with heq | hlt
    · rw [heq]; exact hfin
    · rcases Nat.eq_zero_or_pos s with hs0 | hs1
      · -- the cutoff is `0`, so the degrees below it are negative and local cohomology vanishes
        have hneg : i < 0 := by omega
        have := subsingleton_localCohomologyWithSupportIn_single_of_neg.{u, u} A
          (PrimeSpectrum.zeroLocus (I : Set A)) (ModuleCat.of A M) i hneg
        infer_instance
      · -- the cutoff is positive, so `i ≤ s - 1` and the first half applies
        refine finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff A hA I M
          (s - 1) ?_ i (by omega)
        rw [hs]
        exact_mod_cast Nat.sub_lt hs1 Nat.one_pos
  have := (finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff A hA I s M).mp hall
  rw [hs] at this
  exact lt_irrefl _ this

/-- **Stacks Project, Tag 0BJU.** Let `A` be a Gorenstein Noetherian local ring, let `I ⊆ A` be
an ideal, let `Z = V(I)` and let `M` be a finite `A`-module. Let `s = s_{A,I}(M)` be the cutoff
of Tag 0BJR. Then `H^i_Z(M)` is finite for every `i < s`, and `H^s_Z(M)` is not finite.

This is a special case of Satz 1 of Faltings, and it is obtained here as the special case
`omega = A[0]` of Faltings' finiteness criterion of Tag 0EFD, Gorensteinness of a Noetherian
local ring being precisely the statement that `A[0]` is a dualizing complex.

The first conjunct expresses `i < s` through a natural number `n` with `n < s` and `i ≤ n`; this
covers every degree when `s = ⊤`. The second conjunct is hypothesized on `s` being a natural
number, as it must be: the cutoff is an infimum in `ℕ∞` and there is no degree `⊤`. -/
@[stacks 0BJU]
public theorem finite_lt_and_not_finite_localCohomologyCutoff
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Dualizing.IsGorensteinLocalRing A) (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (∀ n : ℕ, (n : ℕ∞) < localCohomologyCutoff A I M → ∀ i : ℤ, i ≤ (n : ℤ) →
        Module.Finite A
          (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i)) ∧
      (∀ s : ℕ, localCohomologyCutoff A I M = (s : ℕ∞) →
        ¬ Module.Finite A
          (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A M)) (s : ℤ))) :=
  ⟨fun n hn i hi =>
      finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff A hA I M n hn i hi,
    fun s hs => not_finite_localCohomologyWithSupportIn_localCohomologyCutoff A hA I M s hs⟩

end Stacks.LocalCohomology

end
