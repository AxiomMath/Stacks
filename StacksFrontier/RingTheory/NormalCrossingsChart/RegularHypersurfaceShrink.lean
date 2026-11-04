module

public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
public import StacksFrontier.RingTheory.Regular.SingularLocus

/-!
# Shrinking to a regular principal hypersurface

Let `B` be a commutative ring and `y : B`. The locus of primes `q ∋ y` at which the quotient
`B_q / (y)` is a regular local ring is the regular locus of `Spec (B ⧸ (y))`, so when `B ⧸ (y)` is
J-1 that locus is open: a point of it lies in a basic open all of whose points lie in it.

## Main definitions

* `Stacks.NormalCrossingsChart.quotPoint`: the point of `Spec (B ⧸ (y))` under a point of
  `Spec B` at which `y` vanishes.

## Main results

* `Stacks.NormalCrossingsChart.isRegularLocalRing_quotient_iff_atPrime`: regularity of `S / (y)`
  for `S` a localization of `B` at a prime `q ∋ y` is regularity of the local ring of `B ⧸ (y)`
  at the corresponding point; in particular it does not depend on the model `S`.
* `Stacks.NormalCrossingsChart.isDomain_and_isIntegrallyClosed_quotient_iff_atPrime`: the same
  for being an integrally closed domain.
* `Stacks.NormalCrossingsChart.exists_notMem_forall_isRegularLocalRing_quotient_of_isJ1`: when
  `B ⧸ (y)` is J-1, regularity of the quotient by `y` at a prime `q ∋ y` holds at every prime
  `q' ∋ y` of a basic open neighbourhood of `q`.

## References

* [Stacks Project, Tag 0CBS](https://stacks.math.columbia.edu/tag/0CBS)
* [Stacks Project, Tag 07P7](https://stacks.math.columbia.edu/tag/07P7)
-/

@[expose] public section

universe u

namespace Stacks.NormalCrossingsChart

variable {B : Type u} [CommRing B]

private theorem span_le_of_mem {y : B} {q : Ideal B} (hy : y ∈ q) :
    (Ideal.span {y} : Ideal B) ≤ q :=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy)

/-- For `y ∈ q`, the image of `q` in `B ⧸ (y)` pulls back to `q`. -/
public theorem comap_map_quot {y : B} {q : Ideal B} (hy : y ∈ q) :
    (q.map (Ideal.Quotient.mk (Ideal.span {y} : Ideal B))).comap
        (Ideal.Quotient.mk (Ideal.span {y} : Ideal B)) = q :=
  Ideal.comap_map_mk (span_le_of_mem hy)

/-- For a prime `q ∋ y`, the image of `q` in `B ⧸ (y)` is prime. -/
public theorem isPrime_map_quot {y : B} {q : Ideal B} [q.IsPrime] (hy : y ∈ q) :
    (q.map (Ideal.Quotient.mk (Ideal.span {y} : Ideal B))).IsPrime :=
  Ideal.isPrime_map_quotientMk_of_isPrime (span_le_of_mem hy)

/-- The point of `Spec (B ⧸ (y))` under a point of `Spec B` at which `y` vanishes. -/
public noncomputable def quotPoint (y : B) (q : PrimeSpectrum B) (hy : y ∈ q.asIdeal) :
    PrimeSpectrum (B ⧸ (Ideal.span {y} : Ideal B)) :=
  ⟨q.asIdeal.map (Ideal.Quotient.mk (Ideal.span {y} : Ideal B)), isPrime_map_quot hy⟩

private theorem mem_quotPoint_iff {y : B} {q : PrimeSpectrum B} (hy : y ∈ q.asIdeal) (t : B) :
    Ideal.Quotient.mk (Ideal.span {y} : Ideal B) t ∈ (quotPoint y q hy).asIdeal
      ↔ t ∈ q.asIdeal := by
  conv_rhs => rw [← comap_map_quot hy]
  exact Ideal.mem_comap.symm

/-- For `S` a localization of `B` at a prime `q` containing `y`, the ring `S / (y)` is isomorphic
to the localization of `B ⧸ (y)` at the image of `q`. -/
private theorem nonempty_ringEquiv_quotient_atPrime (y : B) (q : PrimeSpectrum B)
    (hy : y ∈ q.asIdeal) (S : Type u) [CommRing S] [Algebra B S]
    [IsLocalization.AtPrime S q.asIdeal] :
    Nonempty ((S ⧸ Ideal.span {algebraMap B S y}) ≃+*
      Localization.AtPrime (quotPoint y q hy).asIdeal) := by
  have hmap : (Ideal.span {y} : Ideal B).map (algebraMap B S) = Ideal.span {algebraMap B S y} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hloc : IsLocalization.AtPrime
      (S ⧸ (Ideal.span {y} : Ideal B).map (algebraMap B S)) (quotPoint y q hy).asIdeal :=
    isLocalization_atPrime_quotient q.asIdeal S (Ideal.span {y}) (quotPoint y q hy).asIdeal
      (comap_map_quot hy)
  rw [← hmap]
  exact ⟨(IsLocalization.algEquiv (quotPoint y q hy).asIdeal.primeCompl
    (S ⧸ (Ideal.span {y} : Ideal B).map (algebraMap B S))
    (Localization.AtPrime (quotPoint y q hy).asIdeal)).toRingEquiv⟩

/-- For `S` a localization of `B` at a prime `q` containing `y`, the ring `S / (y)` is a regular
local ring if and only if the localization of `B ⧸ (y)` at the image of `q` is. -/
public theorem isRegularLocalRing_quotient_iff_atPrime (y : B) (q : PrimeSpectrum B)
    (hy : y ∈ q.asIdeal) (S : Type u) [CommRing S] [Algebra B S]
    [IsLocalization.AtPrime S q.asIdeal] :
    IsRegularLocalRing (S ⧸ Ideal.span {algebraMap B S y}) ↔
      IsRegularLocalRing (Localization.AtPrime (quotPoint y q hy).asIdeal) := by
  obtain ⟨e⟩ := nonempty_ringEquiv_quotient_atPrime y q hy S
  exact ⟨fun _ ↦ IsRegularLocalRing.of_ringEquiv e,
    fun _ ↦ IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- For `S` a localization of `B` at a prime `q` containing `y`, the ring `S / (y)` is an
integrally closed domain if and only if the localization of `B ⧸ (y)` at the image of `q` is. -/
public theorem isDomain_and_isIntegrallyClosed_quotient_iff_atPrime (y : B)
    (q : PrimeSpectrum B) (hy : y ∈ q.asIdeal) (S : Type u) [CommRing S] [Algebra B S]
    [IsLocalization.AtPrime S q.asIdeal] :
    (IsDomain (S ⧸ Ideal.span {algebraMap B S y}) ∧
        IsIntegrallyClosed (S ⧸ Ideal.span {algebraMap B S y})) ↔
      (IsDomain (Localization.AtPrime (quotPoint y q hy).asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime (quotPoint y q hy).asIdeal)) := by
  obtain ⟨e⟩ := nonempty_ringEquiv_quotient_atPrime y q hy S
  exact ⟨fun ⟨_, _⟩ ↦ ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e⟩,
    fun ⟨_, _⟩ ↦ ⟨e.injective.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩⟩

/-- Let `y : B` and suppose the quotient `B ⧸ (y)` is J-1, i.e. its regular locus is open. If
the quotient by `y` of a localization of `B` at a prime `q ∋ y` is a regular local ring, then there
is `t ∉ q` such that the same holds at every prime `q' ∋ y` with `t ∉ q'`. -/
public theorem exists_notMem_forall_isRegularLocalRing_quotient_of_isJ1 (y : B)
    (hJ1 : IsJ1 (B ⧸ (Ideal.span {y} : Ideal B))) (q : PrimeSpectrum B) (hy : y ∈ q.asIdeal)
    (S : Type u) [CommRing S] [Algebra B S] [IsLocalization.AtPrime S q.asIdeal]
    (hreg : IsRegularLocalRing (S ⧸ Ideal.span {algebraMap B S y})) :
    ∃ t ∉ q.asIdeal, ∀ (q' : PrimeSpectrum B), t ∉ q'.asIdeal → y ∈ q'.asIdeal →
      ∀ (S' : Type u) [CommRing S'] [Algebra B S'] [IsLocalization.AtPrime S' q'.asIdeal],
        IsRegularLocalRing (S' ⧸ Ideal.span {algebraMap B S' y}) := by
  classical
  set R := B ⧸ (Ideal.span {y} : Ideal B)
  set E : Set (PrimeSpectrum R) := {x | IsRegularLocalRing (Localization.AtPrime x.asIdeal)}
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff E).mp hJ1
  have hnot : ¬ s ⊆ ((quotPoint y q hy).asIdeal : Set R) := by
    rw [← PrimeSpectrum.mem_zeroLocus, ← hs]
    exact fun h ↦ h ((isRegularLocalRing_quotient_iff_atPrime y q hy S).mp hreg)
  obtain ⟨r, hrs, hrq⟩ := Set.not_subset.mp hnot
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨t, (mem_quotPoint_iff hy t).not.mp hrq, fun q' htq' hyq' S' _ _ _ ↦ ?_⟩
  refine (isRegularLocalRing_quotient_iff_atPrime y q' hyq' S').mpr ?_
  by_contra hc
  have hz : quotPoint y q' hyq' ∈ PrimeSpectrum.zeroLocus s := by rw [← hs]; exact hc
  exact ((mem_quotPoint_iff hyq' t).not.mpr htq') ((PrimeSpectrum.mem_zeroLocus _ _).mp hz hrs)

end Stacks.NormalCrossingsChart

end
