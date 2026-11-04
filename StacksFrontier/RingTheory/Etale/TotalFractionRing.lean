module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.RingTheory.Etale.Height
public import StacksFrontier.RingTheory.Flat.NonZeroDivisors

/-!
# The total ring of fractions of an étale algebra

Let `A` be a commutative ring with finitely many minimal primes every zerodivisor of which lies
in one of them, and let `A → B` be étale. Then the localization of `B` at the image of the
nonzerodivisors of `A` is already the total ring of fractions of `B`:

`Q(A) ⊗_A B = Q(B)`.

The reason is that a prime of `B` meeting no element of the image of the nonzerodivisors of `A`
is a minimal prime of `B`. Indeed such a prime lies over a prime of `A` consisting of
zerodivisors, hence contained in the union of the finitely many minimal primes of `A`, hence —
by prime avoidance — equal to one of them; and an étale ring map preserves the height of a
prime (Stacks 07QP), so the prime of `B` has height zero as well. Every element of a minimal
prime is a zerodivisor, so a nonzerodivisor of `B` lies in no such prime and is therefore
inverted.

## Main results

* `mem_minimalPrimes_of_disjoint_nonZeroDivisors`: a prime of `A` containing no nonzerodivisor
  is a minimal prime, when the zerodivisors of `A` are covered by its finitely many minimal
  primes.
* `IsLocalization.nonZeroDivisors_of_etale`: the localization of `B` at the image of the
  nonzerodivisors of `A` is the total ring of fractions of `B`.
* `IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_etale`: the same statement read on a
  total ring of fractions of `B`, which is the form `Q(A) ⊗_A B = Q(B)` takes once the left
  hand side is recognized as a localization of `B` at the image submonoid.

## Implementation notes

The hypothesis that the zerodivisors of `A` are covered by its minimal primes is the
conjunction of Stacks 05C3, which identifies the zerodivisors with the union of the weakly
associated primes, with the assumption that every weakly associated prime of `A` is minimal.
It is phrased here elementwise, without reference to weakly associated primes, so that this
file depends only on the étale height invariance of Stacks 07QP.

The conclusion is stated as `IsLocalization` of the nonzerodivisors rather than as an
isomorphism `Q(A) ⊗_A B ≃ Q(B)`, which it implies: the tensor product is a localization of `B`
at the image submonoid by `IsLocalization.tensorRight`, and two localizations of `B` at
submonoids with the same localization are canonically isomorphic.

## References

* [Stacks Project, Tag 05C3](https://stacks.math.columbia.edu/tag/05C3)
* [Stacks Project, Tag 07QP](https://stacks.math.columbia.edu/tag/07QP)
-/

@[expose] public section

open scoped nonZeroDivisors

/-- A prime ideal of `A` which contains no nonzerodivisor is a minimal prime, provided the
zerodivisors of `A` are covered by the finitely many minimal primes of `A`.

By prime avoidance the prime is contained in one of the minimal primes, and a prime contained in
a minimal prime is that minimal prime. -/
theorem mem_minimalPrimes_of_disjoint_nonZeroDivisors {A : Type*} [CommRing A]
    (hfin : (minimalPrimes A).Finite)
    (hzd : ∀ a : A, a ∉ A⁰ → ∃ q ∈ minimalPrimes A, a ∈ q)
    (p : Ideal A) [hp : p.IsPrime] (hdisj : Disjoint (p : Set A) (A⁰ : Set A)) :
    p ∈ minimalPrimes A := by
  have hsub : (p : Set A) ⊆ ⋃ q ∈ hfin.toFinset, (q : Set A) := by
    intro a ha
    obtain ⟨q, hq, haq⟩ := hzd a fun h => (hdisj.le_bot ⟨ha, h⟩ : a ∈ (⊥ : Set A)).elim
    exact Set.mem_biUnion (hfin.mem_toFinset.mpr hq) haq
  obtain ⟨i, -, -⟩ := Set.mem_iUnion₂.mp (hsub (p.zero_mem : (0 : A) ∈ (p : Set A)))
  obtain ⟨q, hqmem, hle⟩ := (Ideal.subset_union_prime i i
    (fun j hj _ _ => (hfin.mem_toFinset.mp hj).1.1)).mp (by simpa using hsub)
  have hq := hfin.mem_toFinset.mp hqmem
  have hpq : p = q := le_antisymm hle (hq.2 ⟨hp, bot_le⟩ hle)
  rw [hpq]
  exact hq

/-- The image in an étale `A`-algebra `B` of the nonzerodivisors of `A` is contained in the
nonzerodivisors of `B`, because an étale algebra is flat. -/
theorem Algebra.algebraMapSubmonoid_nonZeroDivisors_le {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] :
    Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ := by
  rintro _ ⟨a, ha, rfl⟩
  exact algebraMap_mem_nonZeroDivisors_of_flat ha

/-- A prime of an étale `A`-algebra `B` which contains no element of the image of the
nonzerodivisors of `A` is a minimal prime of `B`.

It lies over a prime of `A` containing no nonzerodivisor, which is a minimal prime by
`mem_minimalPrimes_of_disjoint_nonZeroDivisors`; an étale ring map preserves heights of primes
(Stacks 07QP), so the prime of `B` has height zero too. -/
theorem mem_minimalPrimes_of_disjoint_algebraMapSubmonoid_nonZeroDivisors {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (hfin : (minimalPrimes A).Finite)
    (hzd : ∀ a : A, a ∉ A⁰ → ∃ q ∈ minimalPrimes A, a ∈ q)
    (q : Ideal B) [q.IsPrime]
    (hdisj : Disjoint (q : Set B) (Algebra.algebraMapSubmonoid B A⁰ : Set B)) :
    q ∈ minimalPrimes B := by
  have hpprime : (q.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  have hdisjA : Disjoint ((q.comap (algebraMap A B) : Ideal A) : Set A) (A⁰ : Set A) := by
    rw [Set.disjoint_left]
    intro a hap ha
    exact (Set.disjoint_left.mp hdisj) (show algebraMap A B a ∈ q from hap) ⟨a, ha, rfl⟩
  have hpmin : q.comap (algebraMap A B) ∈ minimalPrimes A :=
    mem_minimalPrimes_of_disjoint_nonZeroDivisors hfin hzd _ hdisjA
  have hlies : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
  have hph : (q.comap (algebraMap A B)).height = 0 := Ideal.height_eq_zero_iff.mpr hpmin
  have hqh : q.height = 0 :=
    le_antisymm (hph ▸ Ideal.height_le_height_of_liesOver_of_etale _ q) (by simp)
  exact Ideal.height_eq_zero_iff.mp hqh

/-- **The total ring of fractions of an étale algebra.** Let `A` have finitely many minimal
primes, every zerodivisor lying in one of them, and let `B` be an étale `A`-algebra. Then a
localization `T` of `B` at the image of the nonzerodivisors of `A` is already the localization
of `B` at all of its nonzerodivisors, that is the total ring of fractions of `B`.

A nonzerodivisor of `B` which were not inverted in `T` would lie in a prime of `B` meeting no
element of the image submonoid, hence in a minimal prime of `B` by
`mem_minimalPrimes_of_disjoint_algebraMapSubmonoid_nonZeroDivisors`, contradicting that no
element of a minimal prime is a nonzerodivisor. -/
theorem IsLocalization.nonZeroDivisors_of_etale {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B]
    (hfin : (minimalPrimes A).Finite)
    (hzd : ∀ a : A, a ∉ A⁰ → ∃ q ∈ minimalPrimes A, a ∈ q)
    (T : Type*) [CommRing T] [Algebra B T]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) T] :
    IsLocalization B⁰ T := by
  refine IsLocalization.of_le _ _
    (Algebra.algebraMapSubmonoid_nonZeroDivisors_le (A := A) (B := B)) fun r hr => ?_
  by_contra hunit
  obtain ⟨m, hmax, hm⟩ := Ideal.exists_le_maximal (Ideal.span {algebraMap B T r})
    (fun h => hunit (Ideal.span_singleton_eq_top.mp h))
  have hrm : algebraMap B T r ∈ m := hm (Ideal.subset_span rfl)
  have hqprime : (m.comap (algebraMap B T)).IsPrime :=
    have := hmax.isPrime
    Ideal.IsPrime.comap _
  have hdisj : Disjoint ((m.comap (algebraMap B T) : Ideal B) : Set B)
      (Algebra.algebraMapSubmonoid B A⁰ : Set B) := by
    rw [Set.disjoint_left]
    intro b hbm hbS
    exact hmax.ne_top (m.eq_top_of_isUnit_mem hbm
      (IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B A⁰) T ⟨b, hbS⟩))
  have hqmin : m.comap (algebraMap B T) ∈ minimalPrimes B :=
    mem_minimalPrimes_of_disjoint_algebraMapSubmonoid_nonZeroDivisors hfin hzd _ hdisj
  exact (Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hqmin))
    (show r ∈ m.comap (algebraMap B T) from hrm) hr

/-- **`Q(A) ⊗_A B = Q(B)` for an étale algebra.** Under the hypotheses of
`IsLocalization.nonZeroDivisors_of_etale`, a total ring of fractions `K` of `B` is also the
localization of `B` at the image of the nonzerodivisors of `A`.

Together with `IsLocalization.tensorRight`, which exhibits `Q(A) ⊗_A B` as that same
localization, this says that the canonical map `Q(A) ⊗_A B → Q(B)` is an isomorphism. -/
theorem IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_etale {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (hfin : (minimalPrimes A).Finite)
    (hzd : ∀ a : A, a ∉ A⁰ → ∃ q ∈ minimalPrimes A, a ∈ q)
    (K : Type*) [CommRing K] [Algebra B K] [IsFractionRing B K] :
    IsLocalization (Algebra.algebraMapSubmonoid B A⁰) K :=
  have : IsLocalization B⁰ (Localization (Algebra.algebraMapSubmonoid B A⁰)) :=
    IsLocalization.nonZeroDivisors_of_etale hfin hzd _
  IsLocalization.isLocalization_of_algEquiv (Algebra.algebraMapSubmonoid B A⁰)
    (IsLocalization.algEquiv B⁰ (Localization (Algebra.algebraMapSubmonoid B A⁰)) K)

end
