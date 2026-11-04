module

public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Primes of an unramified algebra lying over one prime are incomparable

Let `A → B` be essentially of finite type and formally unramified — for instance étale, or an
étale algebra followed by a localization.  Then no two distinct primes of `B` with the same
contraction to `A` are comparable:  the fibres of an unramified ring map are zero-dimensional.

The proof is [Stacks, Tag 00UW] in the form of Mathlib's
`Algebra.FormallyUnramified.map_maximalIdeal`:  if `𝔟` is a prime of `B` lying over `𝔯 ⊆ A`, then
`𝔯 B_𝔟` is the maximal ideal of `B_𝔟`.  A prime `𝔞 ⊆ 𝔟` of `B` with the same contraction contains
`𝔯`, so `𝔞 B_𝔟` is a prime of `B_𝔟` sandwiched between the maximal ideal and itself;  contracting
back gives `𝔞 = 𝔟`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.eq_of_le_of_under_eq_of_formallyUnramified`: two comparable primes
  of `B` with the same contraction to `A` are equal.

## References

* [Stacks Project, Tag 00UW](https://stacks.math.columbia.edu/tag/00UW)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
-/

@[expose] public section

namespace Stacks.WeaklyAssociatedPrimes

open IsLocalRing

/-- **The fibres of an unramified ring map are zero-dimensional.**  If `A → B` is essentially of
finite type and formally unramified and `𝔞 ⊆ 𝔟` are primes of `B` with the same contraction to
`A`, then `𝔞 = 𝔟`. -/
theorem eq_of_le_of_under_eq_of_formallyUnramified {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    {a b : Ideal B} [a.IsPrime] [b.IsPrime] (hab : a ≤ b)
    (hunder : a.comap (algebraMap A B) = b.comap (algebraMap A B)) : a = b := by
  set r : Ideal A := b.comap (algebraMap A B) with hr
  have : r.IsPrime := Ideal.comap_isPrime _ _
  have : b.LiesOver r := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver r b
  have hAr : Algebra.EssFiniteType (Localization.AtPrime r) (Localization.AtPrime b) :=
    .of_comp A _ _
  have hFUb : Algebra.FormallyUnramified A (Localization.AtPrime b) :=
    .comp A B (Localization.AtPrime b)
  have : Algebra.FormallyUnramified (Localization.AtPrime r) (Localization.AtPrime b) :=
    .of_restrictScalars A _ _
  have hlh : IsLocalHom (algebraMap (Localization.AtPrime r) (Localization.AtPrime b)) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom r b (algebraMap A B) rfl
  -- `𝔯 B_𝔟` is the maximal ideal of `B_𝔟`
  have hmax : Ideal.map (algebraMap A (Localization.AtPrime b)) r
      = maximalIdeal (Localization.AtPrime b) := by
    have h := Algebra.FormallyUnramified.map_maximalIdeal
      (R := Localization.AtPrime r) (S := Localization.AtPrime b)
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal r (Localization.AtPrime r), Ideal.map_map,
      ← IsScalarTower.algebraMap_eq] at h
    exact h
  -- `𝔞 B_𝔟` is a prime ideal, and it contains `𝔯 B_𝔟`
  have hdisj : Disjoint (b.primeCompl : Set B) (a : Set B) :=
    Set.disjoint_left.mpr fun x hx hxa => hx (hab hxa)
  have hap : (a.map (algebraMap B (Localization.AtPrime b))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint b.primeCompl _ a inferInstance hdisj
  have hcomap : (a.map (algebraMap B (Localization.AtPrime b))).comap
      (algebraMap B (Localization.AtPrime b)) = a :=
    IsLocalization.under_map_of_isPrime_disjoint b.primeCompl _ inferInstance hdisj
  have hle : maximalIdeal (Localization.AtPrime b)
      ≤ a.map (algebraMap B (Localization.AtPrime b)) := by
    rw [← hmax, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A B (Localization.AtPrime b)]
    refine Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp ?_)
    rw [hunder]
    exact hx
  have htop : a.map (algebraMap B (Localization.AtPrime b))
      = maximalIdeal (Localization.AtPrime b) :=
    le_antisymm (le_maximalIdeal hap.ne_top) hle
  rw [← hcomap, htop]
  exact IsLocalization.AtPrime.under_maximalIdeal (S := Localization.AtPrime b) (I := b)

end Stacks.WeaklyAssociatedPrimes

end
