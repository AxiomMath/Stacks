module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds

/-!
# Kronecker's bound on the arithmetic rank, and the resulting cohomological dimension bound

Let `A` be a Noetherian ring of Krull dimension at most `d`. Then the zero locus of an arbitrary
ideal `I ⊆ A` is already the zero locus of `d + 1` elements of `I`. This is Kronecker's bound on
the arithmetic rank of an ideal; it is a statement of commutative algebra, and it is what converts
the generator bound on cohomological dimension (Stacks 0DX9 (2)) into a bound by the dimension of
the ring.

The proof is the usual prime-avoidance induction. One builds `f₁, …, f_j ∈ I` such that every
minimal prime `𝔭` of `(f₁, …, f_j)` that does *not* contain `I` has height at least `j`. The
inductive step chooses `f_{j+1} ∈ I` outside the finitely many minimal primes of `(f₁, …, f_j)`
that do not contain `I` (possible by prime avoidance, since `I` is contained in none of them); a
minimal prime of `(f₁, …, f_{j+1})` not containing `I` then strictly contains one of them, so its
height has grown by at least one. After `d + 1` steps no minimal prime can fail to contain `I`,
because its height would exceed `d`.

## Main results

* `Stacks.ArithmeticRank.exists_finset_card_le_succ_zeroLocus_eq` — Kronecker's bound: in a
  Noetherian ring of Krull dimension at most `d`, every ideal contains at most `d + 1` elements
  with the same zero locus.
* `Stacks.ArithmeticRank.exists_finset_card_le_zeroLocus_eq_of_isLocalRing` — over a *local* ring
  and for a *proper* ideal the sharp bound `d` holds.
* `Stacks.ArithmeticRank.exists_zeroLocus_range_eq_of_ringKrullDim_le` and
  `Stacks.ArithmeticRank.exists_zeroLocus_range_eq_of_isLocalRing` — the same two statements with
  the elements presented as a family indexed by a `Fin`, which is the shape the cohomological
  dimension bounds consume.
* `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_succ` — the cohomological
  dimension of a finitely generated ideal of a Noetherian ring is at most `dim A + 1`.

## Implementation notes

The bound `d + 1` is the best possible over a general ring: the `d`-element form is false, as
`Stacks.LocalCohomology.not_forall_exists_zeroLocus_generators_card_le` shows for the unit ideal
of a field, where `V(⊤) = ∅` while the empty family cuts out all of `Spec`. Over a *local* ring
the unit ideal is the only obstruction, and excluding it recovers the sharp bound `d`: a minimal
prime of the chosen ideal of height at least `d` must be the maximal ideal, which contains every
proper ideal. That sharp local form is what bounds the cohomological dimension by `dim A` rather
than by `dim A + 1` after localizing at every prime.

No `@[stacks]` attribute is placed. Kronecker's bound is an input the Stacks project cites from
commutative algebra rather than a tagged result of the chapter.

## References

* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
-/

@[expose] public noncomputable section

universe u

open PrimeSpectrum

namespace Stacks.ArithmeticRank

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The prime-avoidance induction behind Kronecker's bound: for every `j` there are at most `j`
elements of `I` such that every minimal prime of the ideal they generate either contains `I` or
has height at least `j`.

The elements are built one at a time, each chosen inside `I` and outside the finitely many
minimal primes of the previous stage that do not contain `I`. -/
theorem exists_finset_card_le_height_le (I : Ideal A) (j : ℕ) :
    ∃ s : Finset A, ↑s ⊆ (I : Set A) ∧ s.card ≤ j ∧
      ∀ p ∈ (Ideal.span (s : Set A)).minimalPrimes, ¬ I ≤ p → (j : ℕ∞) ≤ p.height := by
  classical
  induction j with
  | zero => exact ⟨∅, by simp, by simp, fun p _ _ => by simp⟩
  | succ j ih =>
    obtain ⟨s, hsI, hscard, hs⟩ := ih
    set S : Set (Ideal A) :=
      {p | p ∈ (Ideal.span (s : Set A)).minimalPrimes ∧ ¬ I ≤ p} with hSdef
    have hfin : S.Finite :=
      (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span (s : Set A))).subset
        (fun p hp => hp.1)
    have hnotsub : ¬ ((I : Set A) ⊆ ⋃ p ∈ (hfin.toFinset : Set (Ideal A)), (p : Set A)) := by
      intro hsub
      obtain ⟨p, hp, hle⟩ :=
        (Ideal.subset_union_prime (f := fun q : Ideal A => q) ⊥ ⊥
          (fun q hq _ _ => ((hfin.mem_toFinset).mp hq).1.isPrime)).mp hsub
      exact ((hfin.mem_toFinset).mp hp).2 hle
    obtain ⟨g, hgI, hg⟩ := Set.not_subset.mp hnotsub
    have hgS : ∀ p ∈ S, g ∉ p := fun p hp hmem =>
      hg (Set.mem_biUnion ((hfin.mem_toFinset).mpr hp) hmem)
    refine ⟨insert g s, ?_, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hgI hsI
    · intro p hp hpI
      have hprime : p.IsPrime := hp.isPrime
      have hspan : Ideal.span (s : Set A) ≤ Ideal.span ((insert g s : Finset A) : Set A) := by
        refine Ideal.span_mono ?_
        rw [Finset.coe_insert]
        exact Set.subset_insert _ _
      obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (hspan.trans hp.le)
      have hqI : ¬ I ≤ q := fun h => hpI (h.trans hqp)
      have hjq : (j : ℕ∞) ≤ q.height := hs q hq hqI
      have hgp : g ∈ p :=
        hp.le (Ideal.subset_span (by rw [Finset.coe_insert]; exact Set.mem_insert _ _))
      have hqlt : q < p := lt_of_le_of_ne hqp fun h => hgS q ⟨hq, hqI⟩ (h ▸ hgp)
      have hqprime : q.IsPrime := hq.isPrime
      push_cast
      exact Order.add_one_le_of_lt
        (lt_of_le_of_lt hjq (Ideal.height_strict_mono_of_isPrime_of_isPrime hqlt))

omit [IsNoetherianRing A] in
/-- A family of elements of `I` whose generated ideal has every minimal prime containing `I` cuts
out the zero locus of `I`: one inclusion is antitonicity of the zero locus, and the other holds
because every prime containing the family contains a minimal prime over it. -/
theorem zeroLocus_eq_of_forall_minimalPrimes {s : Finset A} {I : Ideal A}
    (hsI : ↑s ⊆ (I : Set A))
    (key : ∀ p ∈ (Ideal.span (s : Set A)).minimalPrimes, I ≤ p) :
    zeroLocus ((Ideal.span (s : Set A) : Ideal A) : Set A) = zeroLocus (I : Set A) := by
  refine le_antisymm ?_ (zeroLocus_anti_mono (by exact_mod_cast Ideal.span_le.mpr hsI))
  intro q hq
  rw [mem_zeroLocus] at hq ⊢
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (show Ideal.span (s : Set A) ≤ _ from hq)
  exact (key p hp).trans hpq

omit [IsNoetherianRing A] in
/-- The height of a prime ideal of a ring of Krull dimension at most `d` is at most `d`. -/
theorem height_le_of_ringKrullDim_le {p : Ideal A} [p.IsPrime] {d : ℕ}
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) : p.height ≤ ((d : ℕ) : ℕ∞) := by
  have h : (p.height : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) :=
    Ideal.height_le_ringKrullDim_of_isPrime.trans hd
  exact_mod_cast h

/-- **Kronecker's bound on the arithmetic rank.** In a Noetherian ring of Krull dimension at most
`d`, every ideal `I` contains a set of at most `d + 1` elements whose zero locus is that of `I`.

After `d + 1` steps of `exists_finset_card_le_height_le` no minimal prime of the ideal generated
by the chosen elements can avoid containing `I`: its height would be at least `d + 1`, exceeding
the Krull dimension. -/
theorem exists_finset_card_le_succ_zeroLocus_eq (I : Ideal A) (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    ∃ s : Finset A, ↑s ⊆ (I : Set A) ∧ s.card ≤ d + 1 ∧
      zeroLocus ((Ideal.span (s : Set A) : Ideal A) : Set A) = zeroLocus (I : Set A) := by
  obtain ⟨s, hsI, hscard, hs⟩ := exists_finset_card_le_height_le I (d + 1)
  refine ⟨s, hsI, hscard, zeroLocus_eq_of_forall_minimalPrimes hsI fun p hp => ?_⟩
  by_contra hpI
  have hprime : p.IsPrime := hp.isPrime
  have hcontra := (hs p hp hpI).trans (height_le_of_ringKrullDim_le hd)
  simp only [Nat.cast_le] at hcontra
  omega

/-- **Kronecker's bound over a local ring, with the sharp constant.** In a Noetherian *local* ring
of Krull dimension at most `d`, every *proper* ideal `I` contains a set of at most `d` elements
whose zero locus is that of `I`.

The constant improves on `exists_finset_card_le_succ_zeroLocus_eq` by one because the maximal
ideal is available: a minimal prime of the chosen ideal that fails to contain `I` has height at
least `d`, and a prime of height at least `d` in a local ring of dimension at most `d` must be the
maximal ideal, which contains the proper ideal `I` after all. -/
theorem exists_finset_card_le_zeroLocus_eq_of_isLocalRing [IsLocalRing A] (I : Ideal A)
    (hI : I ≠ ⊤) (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    ∃ s : Finset A, ↑s ⊆ (I : Set A) ∧ s.card ≤ d ∧
      zeroLocus ((Ideal.span (s : Set A) : Ideal A) : Set A) = zeroLocus (I : Set A) := by
  obtain ⟨s, hsI, hscard, hs⟩ := exists_finset_card_le_height_le I d
  refine ⟨s, hsI, hscard, zeroLocus_eq_of_forall_minimalPrimes hsI fun p hp => ?_⟩
  by_contra hpI
  have hprime : p.IsPrime := hp.isPrime
  have hpeq : p = IsLocalRing.maximalIdeal A := by
    by_contra hne
    exact absurd (((hs p hp hpI).trans_lt (Ideal.height_strict_mono_of_isPrime_of_isPrime
      (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p) hne))).trans_le
      (height_le_of_ringKrullDim_le hd)) (lt_irrefl _)
  exact hpI (hpeq ▸ IsLocalRing.le_maximalIdeal hI)

omit [CommRing A] [IsNoetherianRing A] in
/-- A finite set of ring elements, enumerated as a family indexed by `Fin` of its cardinality.
This converts the `Finset` form of Kronecker's bound into the indexed form the cohomological
dimension bounds consume. -/
theorem exists_range_eq_coe (s : Finset A) :
    ∃ f : Fin s.card → A, Set.range f = (s : Set A) := by
  classical
  refine ⟨fun i => (s.equivFin.symm i : A), ?_⟩
  ext a
  refine ⟨?_, fun ha => ⟨s.equivFin ⟨a, ha⟩, by simp⟩⟩
  rintro ⟨i, rfl⟩
  exact (s.equivFin.symm i).2

/-- A bound on a `Finset` cutting out the zero locus of `I` gives the same bound for an indexed
family. -/
private theorem exists_zeroLocus_range_eq_of_finset {B : Type u} [CommRing B] {I : Ideal B} {m : ℕ}
    (h : ∃ s : Finset B, ↑s ⊆ (I : Set B) ∧ s.card ≤ m ∧
      zeroLocus ((Ideal.span (s : Set B) : Ideal B) : Set B) = zeroLocus (I : Set B)) :
    ∃ (n : ℕ) (f : Fin n → B), n ≤ m ∧
      zeroLocus ((Ideal.span (Set.range f) : Ideal B) : Set B) = zeroLocus (I : Set B) := by
  obtain ⟨s, _, hscard, hzl⟩ := h
  obtain ⟨f, hf⟩ := exists_range_eq_coe s
  exact ⟨s.card, f, hscard, hf ▸ hzl⟩

/-- **Kronecker's bound, as an indexed family.** The elements of
`exists_finset_card_le_succ_zeroLocus_eq` presented as a family `Fin n → A` with `n ≤ d + 1`,
which is the shape the generator bounds on cohomological dimension consume. -/
theorem exists_zeroLocus_range_eq_of_ringKrullDim_le (I : Ideal A) (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    ∃ (n : ℕ) (f : Fin n → A), n ≤ d + 1 ∧
      zeroLocus ((Ideal.span (Set.range f) : Ideal A) : Set A) = zeroLocus (I : Set A) := by
  exact exists_zeroLocus_range_eq_of_finset (exists_finset_card_le_succ_zeroLocus_eq I d hd)

/-- **Kronecker's sharp local bound, as an indexed family.** The local counterpart of
`exists_zeroLocus_range_eq_of_ringKrullDim_le`, with `n ≤ d` rather than `n ≤ d + 1`. -/
theorem exists_zeroLocus_range_eq_of_isLocalRing [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤)
    (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    ∃ (n : ℕ) (f : Fin n → A), n ≤ d ∧
      zeroLocus ((Ideal.span (Set.range f) : Ideal A) : Set A) = zeroLocus (I : Set A) := by
  exact exists_zeroLocus_range_eq_of_finset
    (exists_finset_card_le_zeroLocus_eq_of_isLocalRing I hI d hd)

end Stacks.ArithmeticRank

namespace Stacks.LocalCohomology

/-- **The cohomological dimension is bounded by the Krull dimension plus one.** For a finitely
generated ideal `I` of a Noetherian ring `A` of Krull dimension at most `d`, the cohomological
dimension `cd(A, I)` of Stacks 0DX8 is at most `d + 1`.

Kronecker's bound cuts out `V(I)` with `d + 1` elements, and Stacks 0DX9 (2) bounds the
cohomological dimension by the size of any such family. The bound is uniform in `I`: it does not
depend on the ideal, only on the ring. -/
theorem cohomologicalDimension_le_ringKrullDim_succ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ (d : ℤ) + 1 := by
  obtain ⟨n, f, hn, hf⟩ :=
    Stacks.ArithmeticRank.exists_zeroLocus_range_eq_of_ringKrullDim_le I d hd
  refine (cohomologicalDimension_le_card_zeroLocus_generators A I hI f hf).trans ?_
  exact_mod_cast hn

end Stacks.LocalCohomology

end
