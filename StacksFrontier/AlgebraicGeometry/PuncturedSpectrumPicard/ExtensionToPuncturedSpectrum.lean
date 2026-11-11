module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending invertible modules from a neighbourhood to the whole punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`.  Write `U` for the punctured spectrum of
`A` and `U₀` for the punctured closed fibre, the part of `Spec(A/fA)` lying over `U`.
[Stacks, Tag 0F2D] produces, from a class on `U₀`, a class on *some* open `U₀ ⊆ U' ⊆ U`.
[Stacks, Tag 0F2F] upgrades this to all of `U` under the extra hypothesis that for every maximal
ideal `𝔭` of `A_f` the punctured spectrum of `(A_f)_𝔭` has trivial Picard group.

The upgrade is the whole content of the tag, and it has two halves.

**The exceptional set is a finite set of points closed in `U` and maximal in `A_f`.**  Since
`U' ⊇ U₀`, the set `U ∖ U'` misses `V(f)`, so the ideal `I` cut out by `Spec(A) ∖ U'` has the
property that `𝔪` is the only prime containing `I` and `f`.  Krull's principal ideal theorem then
bounds the height of `𝔪` in `A ⧸ I` by one, and that single bound gives everything: a prime of
`V(I)` other than `𝔪` is a minimal prime over `I`, so there are finitely many of them, and the
only prime strictly containing such a prime is `𝔪` — which makes the point closed in `U` and
makes the prime maximal in `A_f`, so that hypothesis (2) applies to it.

**The induction.**  With that in hand, `U'` is obtained from `U` by removing finitely many
points, each removable singly, so a class on `U'` is pushed back to `U` one point at a time.
Each single step is [Stacks, Tag 0F21] together with hypothesis (2) at that point; it is stated
here as `Stacks.PuncturedSpectrumPicard.PicardExtendsAcrossPoint` and proved for every Noetherian
ring as `Stacks.PuncturedSpectrumPicard.picardExtendsAcrossPoint` in
`StacksFrontier/AlgebraicGeometry/PuncturedSpectrumPicard/ExtensionAcrossPoint.lean`.

## Main definitions

* `Stacks.PuncturedSpectrumPicard.complementVanishingIdeal`: the ideal cut out by the
  complement of an open of `Spec A`.
* `Stacks.PuncturedSpectrumPicard.exceptionalPoints`: the points of the punctured spectrum missed by
  an open `U'`, the source's `𝔭₁, …, 𝔭ₙ`.
* `Stacks.PuncturedSpectrumPicard.PicardExtendsAcrossPoint`: the one-point extension step, the
  extension of an invertible module across one point whose local ring has punctured spectrum with
  trivial Picard group.  This is the source's "Limits, Lemma 0F21 applied `n` times" for a single
  `n`; it holds for every Noetherian ring
  (`Stacks.PuncturedSpectrumPicard.picardExtendsAcrossPoint`).

## Main results

* `Stacks.PuncturedSpectrumPicard.finite_exceptionalPoints`,
  `Stacks.PuncturedSpectrumPicard.isOpen_puncturedSpectrum_sdiff_singleton`,
  `Stacks.PuncturedSpectrumPicard.eq_closedPoint_of_lt_of_mem_exceptionalPoints`: the exceptional
  set is finite, its points are closed in the punctured spectrum, and each of them is maximal
  among the primes avoiding `f`, i.e. is a maximal ideal of `A_f`.
* `Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_homOfLE_of_finite`: the
  induction — the one-point step applied to a finite exceptional set.
* `Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_puncturedClosedFibre`: the proof
  of [Stacks, Tag 0F2F] from the conclusion of [Stacks, Tag 0F2D] and the one-point step.  The tag
  itself, under the source's hypotheses, is
  `surjective_schemePullbackClass_puncturedClosedFibre_of_localCohomology`.

## Implementation notes

**Hypothesis (2)** is transcribed with two standard identifications performed in the statement:
a maximal ideal of `A_f` is a prime `𝔭` of `A` with `f ∉ 𝔭` that is maximal among such, and
`(A_f)_𝔭 = A_𝔭 = Localization.AtPrime 𝔭`.  Writing it this way is what lets the induction
consume it without a separate transfer of Picard groups along those isomorphisms.

**The conclusion is surjectivity of `Stacks.Picard.schemePullbackClass` along
`AlgebraicGeometry.morphismRestrict (Stacks.Algebraization.closedImmersion A f)
(Stacks.Divisors.puncturedSpectrum A)`**, the arrow `U₀ ⟶ U`; these are the spellings of
`Stacks.PuncturedSpectrumPicard.PicardColimitSurjective` and of the neighbouring tags of the same
section.

**Opens are indexed over `↥(Spec (CommRingCat.of A))`** rather than over `PrimeSpectrum A`; the
two types are definitionally equal, but the `Set` coercion of an `Opens` of `Spec (.of A)` only
elaborates at the first spelling.

## References

* [Stacks Project, Tag 0F2F](https://stacks.math.columbia.edu/tag/0F2F)
* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 0F21](https://stacks.math.columbia.edu/tag/0F21)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace Stacks.PuncturedSpectrumPicard

/-! ### Primes of a closed set meeting the zero locus of `f` only at the closed point -/

section Algebra

variable {A : Type u} [CommRing A]

/-- Passing to `A ⧸ I` is strictly monotone on the ideals containing `I`, because such an ideal
is recovered from its image by taking the preimage. -/
private theorem map_quotientMk_lt {I p q : Ideal A} (hIp : I ≤ p) (hpq : p < q) :
    p.map (Ideal.Quotient.mk I) < q.map (Ideal.Quotient.mk I) := by
  have hcomap : ∀ J : Ideal A, I ≤ J →
      Ideal.comap (Ideal.Quotient.mk I) (J.map (Ideal.Quotient.mk I)) = J := fun J hJ => by
    rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJ]
  refine lt_of_le_of_ne (Ideal.map_mono hpq.le) fun h => hpq.ne ?_
  rw [← hcomap p hIp, ← hcomap q (hIp.trans hpq.le), h]

/-- Primes `I ≤ p < q` cannot have the image of `q` in `A ⧸ I` of height `< 1`, since the image
of `p` is strictly smaller. -/
private theorem false_of_lt_of_height_map_lt_one {I p q : Ideal A} [p.IsPrime] [q.IsPrime]
    (hIp : I ≤ p) (hpq : p < q) (hq : (q.map (Ideal.Quotient.mk I)).height < (1 : ℕ)) : False :=
  have : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hIp
  have : (q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime (hIp.trans hpq.le)
  absurd (lt_of_le_of_lt (le_add_self.trans
    (Ideal.height_add_one_le_of_lt_of_isPrime (map_quotientMk_lt hIp hpq))) hq) (by simp)

variable [IsLocalRing A]

/-- **The height bound behind the finiteness of the exceptional set.**  Let `A` be a Noetherian
local ring, `f ∈ 𝔪` and `I ≤ 𝔪` an ideal such that the only prime containing both `I` and `f` is
`𝔪`.  Then the image of `𝔪` in `A ⧸ I` has height at most one.

This is Krull's principal ideal theorem in the form
`Ideal.map_height_le_one_of_mem_minimalPrimes`: the hypothesis says exactly that `𝔪` is minimal
over `I ⊔ (f)`. -/
@[ega "0 16.3.2" "special case", ega "IV 5.1.6" "partial"]
theorem height_map_maximalIdeal_le_one [IsNoetherianRing A] {I : Ideal A} {f : A}
    (hf : f ∈ maximalIdeal A)
    (hI : I ≤ maximalIdeal A)
    (hIf : ∀ q : Ideal A, q.IsPrime → I ≤ q → f ∈ q → q = maximalIdeal A) :
    ((maximalIdeal A).map (Ideal.Quotient.mk I)).height ≤ 1 := by
  refine Ideal.map_height_le_one_of_mem_minimalPrimes (x := f) ⟨⟨inferInstance, ?_⟩, ?_⟩
  · exact sup_le hI ((Ideal.span_singleton_le_iff_mem _).mpr hf)
  · intro q hq _
    exact (hIf q hq.1 (le_sup_left.trans hq.2)
      ((Ideal.span_singleton_le_iff_mem _).mp (le_sup_right.trans hq.2))).ge

/-- Under the height bound of `height_map_maximalIdeal_le_one`, a prime containing `I` and
strictly below the maximal ideal has height `< 1` in `A ⧸ I`. -/
private theorem height_map_quotientMk_lt_one {I p : Ideal A} [p.IsPrime]
    [((maximalIdeal A).map (Ideal.Quotient.mk I)).IsPrime]
    (hh : ((maximalIdeal A).map (Ideal.Quotient.mk I)).height ≤ 1)
    (hIp : I ≤ p) (hpm : p < maximalIdeal A) : (p.map (Ideal.Quotient.mk I)).height < (1 : ℕ) :=
  Ideal.height_le_iff.mp hh _ (Ideal.isPrime_map_quotientMk_of_isPrime hIp)
    (map_quotientMk_lt hIp hpm)

/-- Under the height bound of `height_map_maximalIdeal_le_one`, a prime containing `I` and
strictly below the maximal ideal is a minimal prime over `I`: its image in `A ⧸ I` has height
`< 1`, so nothing prime lies strictly below it there. -/
theorem mem_minimalPrimes_of_height_map_le_one {I p : Ideal A} [p.IsPrime]
    (hh : ((maximalIdeal A).map (Ideal.Quotient.mk I)).height ≤ 1)
    (hIp : I ≤ p) (hpm : p < maximalIdeal A) : p ∈ I.minimalPrimes := by
  have : ((maximalIdeal A).map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime (hIp.trans hpm.le)
  refine ⟨⟨inferInstance, hIp⟩, fun q hq hqp => ?_⟩
  by_contra hcon
  have := hq.1
  exact false_of_lt_of_height_map_lt_one hq.2 (lt_of_le_of_ne hqp fun h => hcon h.ge)
    (height_map_quotientMk_lt_one hh hIp hpm)

/-- Under the height bound of `height_map_maximalIdeal_le_one`, the maximal ideal is the only
prime strictly containing a prime that contains `I` and is strictly below the maximal ideal:
a prime strictly between the two would have height `≥ 1` in `A ⧸ I` and height `< 1`. -/
theorem eq_maximalIdeal_of_lt_of_height_map_le_one {I p q : Ideal A} [p.IsPrime] [q.IsPrime]
    (hh : ((maximalIdeal A).map (Ideal.Quotient.mk I)).height ≤ 1)
    (hIp : I ≤ p) (hpm : p < maximalIdeal A) (hpq : p < q) : q = maximalIdeal A := by
  by_contra hne
  have : ((maximalIdeal A).map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime (hIp.trans hpm.le)
  exact false_of_lt_of_height_map_lt_one hIp hpq (height_map_quotientMk_lt_one hh
    (hIp.trans hpq.le) (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹q.IsPrime›)) hne))

end Algebra

/-! ### The exceptional set of a neighbourhood of the punctured closed fibre -/

section Exceptional

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **The ideal cut out by the complement of an open `U` of `Spec A`**: the intersection of the
primes lying outside `U`.  A prime lies outside `U` exactly when it contains this ideal, because
the complement of an open is closed. -/
def complementVanishingIdeal (U : (Spec (CommRingCat.of A)).Opens) : Ideal A :=
  PrimeSpectrum.vanishingIdeal ((U : Set ↥(Spec (CommRingCat.of A)))ᶜ)

omit [IsLocalRing A] in
theorem complementVanishingIdeal_le {U : (Spec (CommRingCat.of A)).Opens} {p : PrimeSpectrum A}
    (hp : p ∉ U) : complementVanishingIdeal U ≤ p.asIdeal :=
  (PrimeSpectrum.mem_zeroLocus _ _).mp
    (PrimeSpectrum.subset_zeroLocus_vanishingIdeal
      ((U : Set ↥(Spec (CommRingCat.of A)))ᶜ) hp)

omit [IsLocalRing A] in
theorem notMem_of_complementVanishingIdeal_le {U : (Spec (CommRingCat.of A)).Opens}
    {p : PrimeSpectrum A} (hp : complementVanishingIdeal U ≤ p.asIdeal) : p ∉ U := by
  have hmem : p ∈ PrimeSpectrum.zeroLocus
      ((complementVanishingIdeal U : Ideal A) : Set A) := (PrimeSpectrum.mem_zeroLocus _ _).mpr hp
  rw [complementVanishingIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hmem
  exact (U.isOpen.isClosed_compl).closure_subset hmem

/-- **The exceptional set of an open `U` of the punctured spectrum**: the points of the punctured
spectrum that `U` misses.  In the proof of [Stacks, Tag 0F2F] this is the set of primes
`𝔭₁, …, 𝔭ₙ` across which the invertible module supplied by [Stacks, Tag 0F2D] still has to be
extended. -/
def exceptionalPoints (A : Type u) [CommRing A] [IsLocalRing A]
    (U : (Spec (CommRingCat.of A)).Opens) : Set ↥(Spec (CommRingCat.of A)) :=
  (Stacks.Divisors.puncturedSpectrum A : Set ↥(Spec (CommRingCat.of A))) \
    (U : Set ↥(Spec (CommRingCat.of A)))

theorem exceptionalPoints_subset (A : Type u) [CommRing A] [IsLocalRing A]
    (U : (Spec (CommRingCat.of A)).Opens) :
    exceptionalPoints A U ⊆
      (Stacks.Divisors.puncturedSpectrum A : Set ↥(Spec (CommRingCat.of A))) :=
  Set.sdiff_subset

variable {U : (Spec (CommRingCat.of A)).Opens} {f : A} {p : PrimeSpectrum A}

theorem ne_closedPoint_of_mem_exceptionalPoints (hp : p ∈ exceptionalPoints A U) :
    p ≠ closedPoint A := hp.1

theorem notMem_of_mem_exceptionalPoints (hp : p ∈ exceptionalPoints A U) : p ∉ U := hp.2

/-- A point of the exceptional set lies in `D(f)`: it is not the closed point, so had it
contained `f` it would have been a point of the punctured closed fibre, hence of `U`. -/
theorem notMem_asIdeal_of_mem_exceptionalPoints
    (hU : ∀ q : PrimeSpectrum A, q ≠ closedPoint A → f ∈ q.asIdeal → q ∈ U)
    (hp : p ∈ exceptionalPoints A U) : f ∉ p.asIdeal := fun hfp =>
  hp.2 (hU p (ne_closedPoint_of_mem_exceptionalPoints hp) hfp)

/-- A point of the exceptional set is not the closed point, so its prime is strictly below the
maximal ideal. -/
theorem lt_maximalIdeal_of_mem_exceptionalPoints (hp : p ∈ exceptionalPoints A U) :
    p.asIdeal < maximalIdeal A :=
  lt_of_le_of_ne (le_maximalIdeal p.isPrime.ne_top) fun h =>
    ne_closedPoint_of_mem_exceptionalPoints hp (PrimeSpectrum.ext h)

variable [IsNoetherianRing A]

/-- The height bound of `height_map_maximalIdeal_le_one` for the ideal cut out by the complement
of a neighbourhood of the punctured closed fibre.  Its hypothesis holds because a prime
containing both that ideal and `f` lies outside `U` and contains `f`, and the only such prime is
the maximal ideal. -/
theorem height_map_maximalIdeal_le_one_complementVanishingIdeal (hf : f ∈ maximalIdeal A)
    (hUle : U ≤ Stacks.Divisors.puncturedSpectrum A)
    (hU : ∀ q : PrimeSpectrum A, q ≠ closedPoint A → f ∈ q.asIdeal → q ∈ U) :
    ((maximalIdeal A).map (Ideal.Quotient.mk (complementVanishingIdeal U))).height ≤ 1 := by
  have hclosed : closedPoint A ∉ U := fun h => (hUle h) rfl
  refine height_map_maximalIdeal_le_one hf (complementVanishingIdeal_le hclosed) ?_
  intro q hq hIq hfq
  by_contra hne
  exact notMem_of_complementVanishingIdeal_le (p := ⟨q, hq⟩) hIq
    (hU ⟨q, hq⟩ (fun h => hne (congrArg PrimeSpectrum.asIdeal h)) hfq)

/-- **The maximal ideal is the only prime strictly containing a point of the exceptional set.**
This is the clause "`𝔭₁, …, 𝔭ₙ` as in (2)" of the source: such a prime avoids `f` and is maximal
among the primes avoiding `f`, that is, it is a maximal ideal of `A_f`.  It is also what makes
the point closed in the punctured spectrum. -/
theorem eq_closedPoint_of_lt_of_mem_exceptionalPoints (hf : f ∈ maximalIdeal A)
    (hUle : U ≤ Stacks.Divisors.puncturedSpectrum A)
    (hU : ∀ q : PrimeSpectrum A, q ≠ closedPoint A → f ∈ q.asIdeal → q ∈ U)
    (hp : p ∈ exceptionalPoints A U) {q : PrimeSpectrum A} (hlt : p.asIdeal < q.asIdeal) :
    q = closedPoint A := by
  have := p.isPrime
  have := q.isPrime
  exact PrimeSpectrum.ext (eq_maximalIdeal_of_lt_of_height_map_le_one
    (height_map_maximalIdeal_le_one_complementVanishingIdeal hf hUle hU)
    (complementVanishingIdeal_le (notMem_of_mem_exceptionalPoints hp))
    (lt_maximalIdeal_of_mem_exceptionalPoints hp) hlt)

/-- **The exceptional set is finite.**  Every one of its points is a minimal prime over the ideal
cut out by the complement of `U`, and a Noetherian ring has only finitely many minimal primes
over an ideal. -/
theorem finite_exceptionalPoints (hf : f ∈ maximalIdeal A)
    (hUle : U ≤ Stacks.Divisors.puncturedSpectrum A)
    (hU : ∀ q : PrimeSpectrum A, q ≠ closedPoint A → f ∈ q.asIdeal → q ∈ U) :
    (exceptionalPoints A U).Finite := by
  refine Set.Finite.of_finite_image (f := PrimeSpectrum.asIdeal)
    (Set.Finite.subset
      (Ideal.finite_minimalPrimes_of_isNoetherianRing A (complementVanishingIdeal U)) ?_)
    fun x _ y _ h => PrimeSpectrum.ext h
  rintro J ⟨q, hq, rfl⟩
  have := q.isPrime
  exact mem_minimalPrimes_of_height_map_le_one
    (height_map_maximalIdeal_le_one_complementVanishingIdeal hf hUle hU)
    (complementVanishingIdeal_le (notMem_of_mem_exceptionalPoints hq))
    (lt_maximalIdeal_of_mem_exceptionalPoints hq)

/-- **A point of the exceptional set is closed in the punctured spectrum**, since the only prime
strictly containing it is the maximal ideal, which the punctured spectrum omits. -/
theorem isOpen_puncturedSpectrum_sdiff_singleton (hf : f ∈ maximalIdeal A)
    (hUle : U ≤ Stacks.Divisors.puncturedSpectrum A)
    (hU : ∀ q : PrimeSpectrum A, q ≠ closedPoint A → f ∈ q.asIdeal → q ∈ U)
    (hp : p ∈ exceptionalPoints A U) :
    IsOpen ((Stacks.Divisors.puncturedSpectrum A : Set ↥(Spec (CommRingCat.of A))) \ {p}) := by
  have hset : (Stacks.Divisors.puncturedSpectrum A :
        Set ↥(Spec (CommRingCat.of A))) \ {p} =
      (Stacks.Divisors.puncturedSpectrum A : Set ↥(Spec (CommRingCat.of A))) ∩
        (PrimeSpectrum.zeroLocus ((p.asIdeal : Ideal A) : Set A))ᶜ := by
    ext q
    constructor
    · rintro ⟨hq, hqp⟩
      refine ⟨hq, fun hle => ?_⟩
      have hle' : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hle
      rcases eq_or_lt_of_le hle' with heq | hlt
      · exact hqp (show q = p from (PrimeSpectrum.ext heq).symm)
      · exact (hq : q ≠ closedPoint A)
          (eq_closedPoint_of_lt_of_mem_exceptionalPoints hf hUle hU hp hlt)
    · rintro ⟨hq, hqz⟩
      refine ⟨hq, fun hmem => hqz ?_⟩
      have hqp : q = p := hmem
      subst hqp
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl
  rw [hset]
  exact (Stacks.Divisors.puncturedSpectrum A).isOpen.inter
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

end Exceptional

/-! ### Extending a Picard class across a finite exceptional set -/

section Induction

/-- **The one-point extension step for the punctured spectrum.**  Let `A` be
a ring, `U` an open of `Spec A`, `𝔭 ∈ U` a point, and `V` the open `U ∖ {𝔭}`.  If the punctured
spectrum of the local ring `A_𝔭` has trivial Picard group, then every invertible module on `V`
is the restriction of an invertible module on `U`.

This is the step the proof of [Stacks, Tag 0F2F] takes from [Stacks, Tag 0F21]: since
`Pic(Spec(A_𝔭) ∖ {𝔭}) = 0`, the given class restricts to the trivial class there, so the trivial
invertible module on `Spec(A_𝔭)` glues to it, and [Stacks, Tag 0F21] — which is in this
library as
`AlgebraicGeometry.GlueingNearPoint.moduleGlueingEquivalenceNearClosedPoint` — turns that
glueing datum into a module on `U`.

It holds for every Noetherian ring: that is
`Stacks.PuncturedSpectrumPicard.picardExtendsAcrossPoint`, proved in
`StacksFrontier/AlgebraicGeometry/PuncturedSpectrumPicard/ExtensionAcrossPoint.lean` through the
translation between `Stacks.Picard.ofScheme` and the category
`AlgebraicGeometry.GlueingNearPoint.FinitePresentationModules` in which [Stacks, Tag 0F21] is
stated, and the identification of `𝒪_{Spec A, 𝔭}` with `A_𝔭`.  It is stated here, for one point
and one open, so that the reduction below can consume it before those ingredients are
imported. -/
def PicardExtendsAcrossPoint (A : Type u) [CommRing A] : Prop :=
  ∀ (V U : (Spec (CommRingCat.of A)).Opens) (p : PrimeSpectrum A), p ∈ U → ∀ hVU : V ≤ U,
    (V : Set ↥(Spec (CommRingCat.of A))) = (U : Set ↥(Spec (CommRingCat.of A))) \ {p} →
    Subsingleton (Stacks.Picard.ofScheme
      (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime p.asIdeal)).toScheme) →
    Function.Surjective
      (Stacks.Picard.schemePullbackClass ((Spec (CommRingCat.of A)).homOfLE hVU))

/-- Removing finitely many points each of which can be removed singly from an open set again
leaves an open set, because `U ∖ Z` is the intersection of `U` with the finitely many open sets
`U ∖ {q}`. -/
theorem isOpen_sdiff_of_finite {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {Z : Set X} (hZ : Z.Finite) (h : ∀ q ∈ Z, IsOpen (U \ {q})) : IsOpen (U \ Z) := by
  have hrw : U \ Z = U ∩ ⋂ q ∈ Z, U \ {q} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_singleton_iff]
    refine ⟨fun hx => ⟨hx.1, fun q hq => ⟨hx.1, fun hxq => hx.2 (hxq ▸ hq)⟩⟩, fun hx => ?_⟩
    exact ⟨hx.1, fun hxZ => (hx.2 x hxZ).2 rfl⟩
  rw [hrw]
  exact hU.inter (hZ.isOpen_biInter h)

variable {A : Type u} [CommRing A]

/-- **"By Limits, Lemma 0F21 applied `n` times".**  If every point of a finite set `Z` of points
of an open `U ⊆ Spec A` can be removed from `U` singly and has local ring with trivially
Picard punctured spectrum, then every invertible module on `U ∖ Z` is the restriction of an
invertible module on `U`.

The induction is on `Z`: removing one more point `a` factors the inclusion
`U ∖ insert a Z' ⊆ U` through `U ∖ Z'`, the first factor is handled by
`PicardExtendsAcrossPoint` at `a` and the second by the inductive hypothesis, and pullback of
Picard classes along a composite is the composite of the pullbacks. -/
theorem surjective_schemePullbackClass_homOfLE_of_finite
    (hstep : PicardExtendsAcrossPoint A) (U : (Spec (CommRingCat.of A)).Opens)
    {Z : Set ↥(Spec (CommRingCat.of A))} (hZfin : Z.Finite) :
    Z ⊆ (U : Set ↥(Spec (CommRingCat.of A))) →
      (∀ q ∈ Z, IsOpen ((U : Set ↥(Spec (CommRingCat.of A))) \ {q})) →
      (∀ q : PrimeSpectrum A, q ∈ Z → Subsingleton (Stacks.Picard.ofScheme
        (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime q.asIdeal)).toScheme)) →
      ∀ (V : (Spec (CommRingCat.of A)).Opens) (hVU : V ≤ U),
        (V : Set ↥(Spec (CommRingCat.of A))) = (U : Set ↥(Spec (CommRingCat.of A))) \ Z →
        Function.Surjective
          (Stacks.Picard.schemePullbackClass ((Spec (CommRingCat.of A)).homOfLE hVU)) := by
  induction Z, hZfin using Set.Finite.induction_on with
  | @empty =>
    intro _ _ _ V hVU hVeq
    have hV : V = U := TopologicalSpace.Opens.ext (by rw [hVeq, Set.sdiff_empty])
    subst hV
    intro c
    refine ⟨c, ?_⟩
    rw [show (Spec (CommRingCat.of A)).homOfLE hVU = CategoryTheory.CategoryStruct.id _ from
      Scheme.homOfLE_rfl _ _]
    exact Stacks.Picard.schemePullbackClass_id _ c
  | @insert a Z' haZ' hZ'fin IH =>
    intro hsub hopen htriv V hVU hVeq
    have hZ'sub : Z' ⊆ (U : Set ↥(Spec (CommRingCat.of A))) :=
      fun x hx => hsub (Set.mem_insert_of_mem _ hx)
    have haU : a ∈ (U : Set ↥(Spec (CommRingCat.of A))) := hsub (Set.mem_insert _ _)
    have hopen' : ∀ q ∈ Z', IsOpen ((U : Set ↥(Spec (CommRingCat.of A))) \ {q}) :=
      fun q hq => hopen q (Set.mem_insert_of_mem _ hq)
    obtain ⟨W, hWset⟩ : ∃ W : (Spec (CommRingCat.of A)).Opens,
        (W : Set ↥(Spec (CommRingCat.of A))) =
          (U : Set ↥(Spec (CommRingCat.of A))) \ Z' :=
      ⟨⟨(U : Set ↥(Spec (CommRingCat.of A))) \ Z', isOpen_sdiff_of_finite U.isOpen hZ'fin
        hopen'⟩, rfl⟩
    have hWU : W ≤ U := by
      intro x hx
      have hx' : x ∈ (W : Set ↥(Spec (CommRingCat.of A))) := hx
      rw [hWset] at hx'
      exact hx'.1
    have hVWset : (V : Set ↥(Spec (CommRingCat.of A))) =
        (W : Set ↥(Spec (CommRingCat.of A))) \ {a} := by
      rw [hVeq, hWset]
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hVW : V ≤ W := by
      intro x hx
      have hx' : x ∈ (V : Set ↥(Spec (CommRingCat.of A))) := hx
      rw [hVWset] at hx'
      exact hx'.1
    have haW : a ∈ W := by
      have : a ∈ (W : Set ↥(Spec (CommRingCat.of A))) := by rw [hWset]; exact ⟨haU, haZ'⟩
      exact this
    have h1 : Function.Surjective (Stacks.Picard.schemePullbackClass
        ((Spec (CommRingCat.of A)).homOfLE hVW)) :=
      hstep V W a haW hVW hVWset (htriv a (Set.mem_insert _ _))
    have h2 := IH hZ'sub hopen'
      (fun q hq => htriv q (Set.mem_insert_of_mem _ hq)) W hWU hWset
    intro c
    obtain ⟨x, hx⟩ := h1.comp h2 c
    refine ⟨x, ?_⟩
    rw [← hx, Function.comp_apply, Stacks.Picard.schemePullbackClass_comp,
      Scheme.homOfLE_homOfLE]

end Induction

/-! ### Surjectivity of `Pic(U) → Pic(U₀)` -/

section Main

/-- Pullback of Picard classes along an isomorphism of schemes is injective, being inverted by
pullback along the inverse isomorphism. -/
theorem schemePullbackClass_injective_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (Stacks.Picard.schemePullbackClass e.hom) := by
  intro a b hab
  have h := congrArg (Stacks.Picard.schemePullbackClass e.inv) hab
  rwa [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    e.inv_hom_id, Stacks.Picard.schemePullbackClass_id,
    Stacks.Picard.schemePullbackClass_id] at h

variable {A : Type u} [CommRing A] [IsLocalRing A] {f : A}

/-- **"Since `U' ⊇ U₀` we see that `U ∖ U'` consists of points … in `D(f)`".**  If the punctured
closed fibre factors through an open `V` of the punctured spectrum, then every prime of `A`
containing `f` other than the maximal ideal lies in the image of `V` in `Spec A`.

Such a prime is in the range of `Spec(A/fA) ⟶ Spec A`, and being distinct from the maximal ideal
its preimage lies in the punctured closed fibre, whose image the factorisation puts inside
`V`. -/
theorem mem_ι_image_of_mem_of_ne {V : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens}
    (j : (Stacks.Algebraization.puncturedClosedFibre A f).toScheme ⟶ V.toScheme)
    (hj : j ≫ V.ι = morphismRestrict (Stacks.Algebraization.closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A))
    (q : PrimeSpectrum A) (hq : q ≠ closedPoint A) (hfq : f ∈ q.asIdeal) :
    q ∈ (Stacks.Divisors.puncturedSpectrum A).ι ''ᵁ V := by
  have hmem : q ∈ PrimeSpectrum.zeroLocus
      ((RingHom.ker (Ideal.Quotient.mk (Ideal.span ({f} : Set A))) : Ideal A) : Set A) := by
    rw [Ideal.mk_ker]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr ((Ideal.span_singleton_le_iff_mem _).mpr hfq)
  rw [← range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective] at hmem
  obtain ⟨q₀, hq₀⟩ := hmem
  have hbase : (Stacks.Algebraization.closedImmersion A f) q₀ = q := by
    have h := Spec.map_apply
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({f} : Set A)))) q₀
    rw [CommRingCat.hom_ofHom] at h
    exact h.trans hq₀
  have hq₀mem : q₀ ∈ Stacks.Algebraization.puncturedClosedFibre A f := by
    change (Stacks.Algebraization.closedImmersion A f) q₀ ∈ Stacks.Divisors.puncturedSpectrum A
    rw [hbase]
    exact hq
  let y : (Stacks.Algebraization.puncturedClosedFibre A f).toScheme := ⟨q₀, hq₀mem⟩
  have hy : morphismRestrict (Stacks.Algebraization.closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A) y ∈ V := by
    rw [← hj, Scheme.Hom.comp_apply]
    exact (j y).2
  have hmemimg := (Scheme.Opens.mem_ι_image_iff
    (Stacks.Divisors.puncturedSpectrum A) (V := V)).mpr hy
  rw [morphismRestrict_base_coe] at hmemimg
  change (Stacks.Algebraization.closedImmersion A f) q₀ ∈
    (Stacks.Divisors.puncturedSpectrum A).ι ''ᵁ V at hmemimg
  rwa [hbase] at hmemimg

variable [IsNoetherianRing A]

/-- **The proof of [Stacks, Tag 0F2F], from [Stacks, Tag 0F2D] and the one-point step.**  Let
`(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`.  Write `U` for the punctured spectrum of `A` and
`U₀` for the punctured closed fibre.  If every class on `U₀` comes from an open `U₀ ⊆ U' ⊆ U`
(`PicardColimitSurjective`, the conclusion of [Stacks, Tag 0F2D]), the one-point extension step
`PicardExtendsAcrossPoint` holds, and every maximal ideal `𝔭` of `A_f` has `Pic` of the punctured
spectrum of `A_𝔭` trivial, then restriction `Pic(U) → Pic(U₀)` is surjective.

Hypothesis `h2` is the source's clause (2), transcribed with the two standard identifications: a
maximal ideal of `A_f` is a prime `𝔭` of `A` with `f ∉ 𝔭` maximal among such, and
`(A_f)_𝔭 = A_𝔭`.  The tag itself, under the source's hypotheses, is
`surjective_schemePullbackClass_puncturedClosedFibre_of_localCohomology`, which supplies the
first input by `picardColimitSurjective` and the second by `picardExtendsAcrossPoint`.

A class on `U₀` comes from a class on some open `U₀ ⊆ U' ⊆ U`.  The
exceptional set `U ∖ U'` is finite and consists of points closed in `U` and maximal in `A_f`
(`finite_exceptionalPoints`, `isOpen_puncturedSpectrum_sdiff_singleton`,
`eq_closedPoint_of_lt_of_mem_exceptionalPoints`), so the class extends across those points one at a
time by `surjective_schemePullbackClass_homOfLE_of_finite`. -/
theorem surjective_schemePullbackClass_puncturedClosedFibre (hf : f ∈ maximalIdeal A)
    (hstep : PicardExtendsAcrossPoint A) (hcolim : PicardColimitSurjective A f)
    (h2 : ∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
      (∀ q : PrimeSpectrum A, p.asIdeal < q.asIdeal → f ∈ q.asIdeal) →
      Subsingleton (Stacks.Picard.ofScheme
        (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime p.asIdeal)).toScheme)) :
    Function.Surjective (Stacks.Picard.schemePullbackClass
      (morphismRestrict (Stacks.Algebraization.closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))) := by
  intro c
  obtain ⟨V, j, hj, cV, hcV⟩ := hcolim c
  have hUle : (Stacks.Divisors.puncturedSpectrum A).ι ''ᵁ V ≤
      Stacks.Divisors.puncturedSpectrum A := (Stacks.Divisors.puncturedSpectrum A).ι_image_le V
  have hU0 : ∀ q : PrimeSpectrum A, q ≠ closedPoint A → f ∈ q.asIdeal →
      q ∈ (Stacks.Divisors.puncturedSpectrum A).ι ''ᵁ V := mem_ι_image_of_mem_of_ne j hj
  have hsurj : Function.Surjective (Stacks.Picard.schemePullbackClass
      ((Spec (CommRingCat.of A)).homOfLE hUle)) := by
    refine surjective_schemePullbackClass_homOfLE_of_finite hstep _
      (finite_exceptionalPoints hf hUle hU0) (exceptionalPoints_subset A _)
      (fun q hq => isOpen_puncturedSpectrum_sdiff_singleton hf hUle hU0 hq) ?_ _ hUle ?_
    · intro q hq
      refine h2 q (notMem_asIdeal_of_mem_exceptionalPoints hU0 hq) fun r hlt => ?_
      have hr := eq_closedPoint_of_lt_of_mem_exceptionalPoints hf hUle hU0 hq hlt
      subst hr
      exact hf
    · rw [exceptionalPoints, Set.sdiff_sdiff_right_self]
      exact (Set.inter_eq_right.mpr hUle).symm
  have hVsurj : Function.Surjective (Stacks.Picard.schemePullbackClass V.ι) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (Stacks.Picard.schemePullbackClass
      ((Stacks.Divisors.puncturedSpectrum A).ι.isoImage V).inv y)
    refine ⟨x, schemePullbackClass_injective_of_iso
      ((Stacks.Divisors.puncturedSpectrum A).ι.isoImage V).symm ?_⟩
    rw [Iso.symm_hom, Stacks.Picard.schemePullbackClass_comp,
      Scheme.Opens.isoImage_ι_inv_ι]
    exact hx
  obtain ⟨cX, hcX⟩ := hVsurj cV
  exact ⟨cX, by rw [← hcV, ← hcX, Stacks.Picard.schemePullbackClass_comp, hj]⟩

end Main

end Stacks.PuncturedSpectrumPicard

end
