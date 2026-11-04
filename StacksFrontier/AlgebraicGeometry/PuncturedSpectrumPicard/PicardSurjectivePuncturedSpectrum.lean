module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.CompleteIntersection
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalPicardAlgebraization

/-!
# Surjectivity of `Pic(U) → Pic(U₀)` for the punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`.  Write `U` for the punctured spectrum of
`A` and `U₀` for the punctured spectrum of `A/fA`.  [Stacks, Tag 0F2F] says that if the
conditions of [Stacks, Tag 0F2D] hold and, for every maximal ideal `𝔭` of `A_f`, the punctured
spectrum of `(A_f)_𝔭` has trivial Picard group, then `Pic(U) → Pic(U₀)` is surjective.

The geometric half of the proof — the complement of the open supplied by [Stacks, Tag 0F2D] is a
finite set of points closed in `U` and maximal in `A_f`, and a class extends across each of them
by [Stacks, Tag 0F21] — is
`surjective_schemePullbackClass_puncturedClosedFibre_of_isNoetherianRing`.  That
declaration reads hypothesis (2) at primes of `A`: for every prime `𝔭` of `A` with `f ∉ 𝔭`,
maximal among such, the punctured spectrum of `A_𝔭` has trivial Picard group.  This file
translates the source's hypothesis (2), stated over the maximal ideals of
`A_f = Localization.Away f`, into that form, and assembles the tag from it and [Stacks, Tag 0F2D],
which is `Stacks.PuncturedSpectrumPicard.picardColimitSurjective`.

## Main results

* `Stacks.PuncturedSpectrumPicard.isMaximal_map_algebraMap_away`: a prime of `A` avoiding `f`
  and maximal among such generates a maximal ideal of `A_f`.
* `Stacks.PuncturedSpectrumPicard.subsingleton_picard_localizationAtPrime_of_away`: hypothesis
  (2) of [Stacks, Tag 0F2F], stated over the maximal ideals of `A_f`, at a prime of `A`.
* `surjective_schemePullbackClass_puncturedClosedFibre_of_localCohomology`: **[Stacks, Tag 0F2F]**.

## Implementation notes

The identification `(A_f)_𝔓 ≅ A_𝔭` for `𝔭` the contraction of `𝔓` is Mathlib's
`IsLocalization.isLocalization_atPrime_localization_atPrime`, and triviality of the Picard group of
a punctured spectrum is transported along it by
`Stacks.PuncturedSpectrumPicard.subsingleton_picard_puncturedSpectrum_of_ringEquiv`.

## References

* [Stacks Project, Tag 0F2F](https://stacks.math.columbia.edu/tag/0F2F)
* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.PuncturedSpectrumPicard

variable {A : Type u} [CommRing A] {f : A}

/-- **A prime of `A` avoiding `f` and maximal among such generates a maximal ideal of `A_f`.**
A maximal ideal of `A_f` above its extension contracts to a prime avoiding `f` that contains it,
hence equals it, and an ideal of a localization is the extension of its contraction. -/
theorem isMaximal_map_algebraMap_away {p : Ideal A} [p.IsPrime] (hfp : f ∉ p)
    (hmax : ∀ q : Ideal A, q.IsPrime → p < q → f ∈ q) :
    (p.map (algebraMap A (Localization.Away f))).IsMaximal := by
  have hd : Disjoint (Submonoid.powers f : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfp
  have hP := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
    (Localization.Away f) p ‹_› hd
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal _ hP.ne_top
  have hcomap : M.comap (algebraMap A (Localization.Away f)) = p := by
    have hle : p ≤ M.comap (algebraMap A (Localization.Away f)) := by
      rw [← IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f)
        (Localization.Away f) ‹p.IsPrime› hd]
      exact Ideal.comap_mono hPM
    refine (eq_of_le_of_not_lt hle fun hlt => ?_).symm
    have hfM := hmax _ (Ideal.comap_isPrime _ M) hlt
    exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hfM
      (IsLocalization.Away.algebraMap_isUnit f))
  have : M = p.map (algebraMap A (Localization.Away f)) := by
    rw [← hcomap]
    exact (IsLocalization.map_under (Submonoid.powers f) (Localization.Away f) M).symm
  exact this ▸ hM

/-- **Hypothesis (2) of [Stacks, Tag 0F2F] at a prime of `A`.**  If for every maximal ideal `𝔓`
of `A_f` the punctured spectrum of `(A_f)_𝔓` has trivial Picard group, then so does the punctured
spectrum of `A_𝔭` for every prime `𝔭` of `A` avoiding `f` and maximal among such: the extension
`𝔓` of `𝔭` to `A_f` is maximal, it contracts to `𝔭`, and `(A_f)_𝔓` is a localization of `A` at
`𝔭`. -/
theorem subsingleton_picard_localizationAtPrime_of_away
    (h2 : ∀ (P : Ideal (Localization.Away f)) [P.IsMaximal],
      Subsingleton (Stacks.Picard.ofScheme
        (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime P)).toScheme))
    (p : PrimeSpectrum A) (hfp : f ∉ p.asIdeal)
    (hmax : ∀ q : PrimeSpectrum A, p.asIdeal < q.asIdeal → f ∈ q.asIdeal) :
    Subsingleton (Stacks.Picard.ofScheme
      (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime p.asIdeal)).toScheme) := by
  have hd := (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfp
  let P := p.asIdeal.map (algebraMap A (Localization.Away f))
  have : P.IsMaximal := isMaximal_map_algebraMap_away hfp fun q hq hlt => hmax ⟨q, hq⟩ hlt
  have : IsLocalization.AtPrime (Localization.AtPrime P) p.asIdeal := by
    convert IsLocalization.isLocalization_atPrime_localization_atPrime _ P
    exact (IsLocalization.under_map_of_isPrime_disjoint _ _ p.isPrime hd).symm
  exact subsingleton_picard_puncturedSpectrum_of_ringEquiv
    (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime P)).toRingEquiv.symm (h2 P)

/-- **[Stacks, Tag 0F2F].**  Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`.  Assume
(1) the conditions of [Stacks, Tag 0F2D]: `A` is `f`-adically complete, `f` is a nonzerodivisor,
`H¹_𝔪(A/fA)` and `H²_𝔪(A/fA)` are finite `A`-modules and `H³_𝔪(A/fA) = 0`; and (2) for every
maximal ideal `𝔓` of `A_f` the punctured spectrum of `(A_f)_𝔓` has trivial Picard group.  Let `U`,
resp. `U₀`, be the punctured spectrum of `A`, resp. `A/fA`.  Then `Pic(U) → Pic(U₀)` is
surjective.

A class on `U₀` comes from a class on an open `U₀ ⊆ U' ⊆ U` by [Stacks, Tag 0F2D]
(`picardColimitSurjective`); the complement `U ∖ U'` is a finite set of points that are maximal
ideals of `A_f`, and the class extends across each of them by [Stacks, Tag 0F21]
(`surjective_schemePullbackClass_puncturedClosedFibre_of_isNoetherianRing`), hypothesis (2)
being read at those points by `subsingleton_picard_localizationAtPrime_of_away`.

`U₀` is `Stacks.Algebraization.puncturedClosedFibre A f`, the part of `Spec(A/fA)` over `U`,
which is the punctured spectrum of `A/fA`
(`Stacks.PuncturedSpectrumPicard.puncturedClosedFibre_eq_puncturedSpectrum_quotient`). -/
@[stacks 0F2F "the full statement: under the four conditions of Stacks 0F2D (f-adic \
completeness, f a nonzerodivisor, finiteness of H^1_m(A/fA) and H^2_m(A/fA), vanishing of \
H^3_m(A/fA)) and triviality of Pic of the punctured spectrum of (A_f)_P for every maximal \
ideal P of A_f, restriction Pic(U) -> Pic(U_0) is surjective"]
theorem surjective_schemePullbackClass_puncturedClosedFibre_of_localCohomology
    [IsLocalRing A] [IsNoetherianRing A] (hf : f ∈ maximalIdeal A)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A) (hreg : IsSMulRegular A f)
    (hH1 : Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 1))
    (hH2 : Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 2))
    (hvanish3 : IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 3))
    (h2 : ∀ (P : Ideal (Localization.Away f)) [P.IsMaximal],
      Subsingleton (Stacks.Picard.ofScheme
        (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime P)).toScheme)) :
    Function.Surjective (Stacks.Picard.schemePullbackClass
      (morphismRestrict (Stacks.Algebraization.closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))) :=
  surjective_schemePullbackClass_puncturedClosedFibre_of_isNoetherianRing hf
    (picardColimitSurjective A f hf hcomplete hreg hH1 hH2 hvanish3)
    fun p hfp hmax => subsingleton_picard_localizationAtPrime_of_away h2 p hfp hmax

end Stacks.PuncturedSpectrumPicard
