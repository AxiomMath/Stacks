module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import StacksFrontier.RingTheory.Localization.UniquePrimeOver

/-!
# Localization at the unique point of a finite fibre

Let `A → B` be a finite ring map and let `p` be a prime of `A`. If `q` is the unique prime of
`B` lying over `p`, then localizing `B` at the image of the complement of `p` localizes `B` at
`q`.

## Main results

* `isLocalization_atPrime_of_primesOver_eq_singleton`: every localization of `B` at the image of
  `A \ p` is a localization of `B` at the unique prime `q` above `p`.
-/
public section

universe u v w

/-- For a finite ring map `A → B`, if `q` is the unique prime of `B` over the prime `p` of `A`,
then any localization of `B` at the image of `A \ p` is a localization of `B` at `q`. -/
theorem isLocalization_atPrime_of_primesOver_eq_singleton
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] {p : Ideal A} {q : Ideal B} [p.IsPrime] [q.IsPrime]
    (hq : p.primesOver B = {q})
    (Bp : Type w) [CommRing Bp] [Algebra B Bp]
    [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) Bp] :
    IsLocalization.AtPrime Bp q := by
  have : q.LiesOver p := ((Set.ext_iff.mp hq q).mpr (Set.mem_singleton q)).2
  have : IsLocalization q.primeCompl
      (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) :=
    localization_eq_of_unique_prime_over p q
      (fun q' hq' hq'p ↦ Set.mem_singleton_iff.mp ((Set.ext_iff.mp hq q').mp ⟨hq', hq'p⟩))
      (Or.inl fun p₁ p₂ q₁ _ _ _ hle hover ↦ by
        have : q₁.LiesOver p₁ := ⟨hover.symm⟩
        obtain ⟨q₂, hle', hq₂, hover'⟩ := Ideal.exists_ideal_ge_liesOver_of_le (P := q₁) hle
        exact ⟨q₂, hq₂, hle', hover'.over.symm⟩)
  exact IsLocalization.isLocalization_of_algEquiv q.primeCompl
    (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B p.primeCompl)
      (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) Bp)
