module

public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.AlgebraicGeometry.StalkMinimalPrimes.Basic

/-!
# The minimal primes of a localization, as an index set

Let `A` be a commutative ring, `M ⊆ A` a submonoid and `Aₘ` a localization of `A` at `M`.  The
minimal primes of `Aₘ` are in bijection with the minimal primes of `A` that are disjoint from
`M`, by contraction and expansion.  When `A` has finitely many minimal primes, a single element
of `M` lies in every minimal prime of `A` that meets `M`.

## Main results

* `Stacks.MinimalPrimeResidueLocalization.minimalPrimesEquivDisjoint`: the minimal primes of a
  localization are in bijection with the minimal primes of the base ring disjoint from the
  localized submonoid.
* `Stacks.MinimalPrimeResidueLocalization.under_minimalPrimesEquivDisjoint`: that bijection
  sends a minimal prime to its contraction.
* `Stacks.MinimalPrimeResidueLocalization.exists_mem_mem_of_not_disjoint`: for a ring with
  finitely many minimal primes, a single element of the submonoid lies in every minimal prime
  that meets the submonoid.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.MinimalPrimeResidueLocalization

variable (A : Type u) [CommRing A] (M : Submonoid A)
variable (Aₘ : Type u) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ]

include M in
/-- The contraction of a minimal prime of a localization is a minimal prime. -/
public theorem under_mem_minimalPrimes {q : Ideal Aₘ} (hq : q ∈ minimalPrimes Aₘ) :
    q.under A ∈ minimalPrimes A := by
  rwa [Stacks.StalkMinimalPrimes.Basic.minimalPrimes_eq_preimage_under_of_isLocalization M Aₘ] at hq

/-- The contraction of a prime of a localization is disjoint from the localized submonoid. -/
public theorem disjoint_under {q : Ideal Aₘ} (hq : q.IsPrime) :
    Disjoint (M : Set A) ((q.under A : Ideal A) : Set A) :=
  (IsLocalization.disjoint_under_iff M Aₘ q).mpr hq.ne_top

/-- The expansion of a minimal prime disjoint from the localized submonoid is a minimal prime of
the localization. -/
public theorem map_mem_minimalPrimes {p : Ideal A} (hp : p ∈ minimalPrimes A)
    (hd : Disjoint (M : Set A) (p : Set A)) :
    p.map (algebraMap A Aₘ) ∈ minimalPrimes Aₘ := by
  rw [Stacks.StalkMinimalPrimes.Basic.minimalPrimes_eq_preimage_under_of_isLocalization M Aₘ]
  change (p.map (algebraMap A Aₘ)).under A ∈ minimalPrimes A
  rwa [IsLocalization.under_map_of_isPrime_disjoint M Aₘ hp.1.1 hd]

/-- The minimal primes of a localization are in bijection with the minimal primes of the base
ring that are disjoint from the localized submonoid. -/
public noncomputable def minimalPrimesEquivDisjoint :
    minimalPrimes Aₘ ≃ {p : minimalPrimes A // Disjoint (M : Set A) ((p : Ideal A) : Set A)} where
  toFun q := ⟨⟨(q : Ideal Aₘ).under A, under_mem_minimalPrimes A M Aₘ q.2⟩,
    disjoint_under A M Aₘ q.2.1.1⟩
  invFun p := ⟨(p.1 : Ideal A).map (algebraMap A Aₘ),
    map_mem_minimalPrimes A M Aₘ p.1.2 p.2⟩
  left_inv q := Subtype.ext (IsLocalization.map_under M Aₘ (q : Ideal Aₘ))
  right_inv p := Subtype.ext (Subtype.ext
    (IsLocalization.under_map_of_isPrime_disjoint M Aₘ p.1.2.1.1 p.2))

/-- The bijection of minimal primes sends a minimal prime of the localization to its
contraction. -/
public theorem under_minimalPrimesEquivDisjoint (q : minimalPrimes Aₘ) :
    ((minimalPrimesEquivDisjoint A M Aₘ q).1 : Ideal A) = (q : Ideal Aₘ).under A :=
  rfl

/-- For a ring with finitely many minimal primes there is a single element of a submonoid lying
in every minimal prime that the submonoid meets. -/
public theorem exists_mem_mem_of_not_disjoint (hA : (minimalPrimes A).Finite) :
    ∃ s ∈ M, ∀ p : minimalPrimes A,
      ¬ Disjoint (M : Set A) ((p : Ideal A) : Set A) → s ∈ (p : Ideal A) := by
  classical
  have : Finite (minimalPrimes A) := hA
  have : Fintype {p : minimalPrimes A // ¬ Disjoint (M : Set A) ((p : Ideal A) : Set A)} :=
    Fintype.ofFinite _
  choose f hfM hfp using fun b :
      {p : minimalPrimes A // ¬ Disjoint (M : Set A) ((p : Ideal A) : Set A)} ↦
    Set.not_disjoint_iff.mp b.2
  refine ⟨∏ b, f b, Submonoid.prod_mem _ fun b _ ↦ hfM b, fun p hp ↦ ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ
    (⟨p, hp⟩ : {p : minimalPrimes A // ¬ Disjoint (M : Set A) ((p : Ideal A) : Set A)}))
  rw [hc]
  exact Ideal.mul_mem_right _ _ (hfp ⟨p, hp⟩)

end Stacks.MinimalPrimeResidueLocalization

end
