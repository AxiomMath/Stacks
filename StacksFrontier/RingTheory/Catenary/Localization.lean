module

public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary

/-!
# Comparing the catenary predicates, and localization

This repository carries two formulations of catenarity for a commutative ring. `Ring.IsCatenary`
asks, for each pair of primes `p ≤ q`, that the chains of primes from `p` to `q` be of bounded
length and that the saturated ones all have one common length. `IsUniversallyCatenary` is phrased
instead through the topological predicate `IrreducibleClosedsCodim.IsCatenarySpace`, which asks
that for each pair of irreducible closed subsets `Y ⊆ Y'` the codimension `topCodim Y Y'` be
finite and that every maximal chain realize it.

The two agree, and this module proves it. The comparison runs through
`Catenary.IsCatenaryOrder`, the order-theoretic form of the condition: a bound on the lengths of
chains plus equality of the lengths of saturated chains. Over `IrreducibleCloseds X` the bound is
exactly finiteness of `topCodim`, and the common saturated length is then forced to equal it.

The payoff is that localization-stability, already available for the topological predicate, holds
for `Ring.IsUniversallyCatenary` as well.

## Main results

* `Ring.isCatenary_iff_isCatenarySpace_primeSpectrum` — `Ring.IsCatenary R` is catenarity of the
  topological space `Spec R`.
* `Ring.isUniversallyCatenary_iff_isUniversallyCatenary` — the two universal-catenarity
  predicates agree.
* `Ring.isUniversallyCatenaryNoetherian_iff_isNoetherianRing_and_isUniversallyCatenary` —
  universal
  catenarity in the sense of Stacks 00NL, compared with the topological predicate.
* `Ring.IsUniversallyCatenary.localization` — a localization of a Noetherian universally catenary
  ring is universally catenary.
* `Ring.isCatenary_and_isUniversallyCatenary_of_isLocalization` — Stacks 00NJ: any localization of
  a catenary ring is catenary, and any localization of a Noetherian universally catenary ring is
  Noetherian and universally catenary.

## References

* [Stacks Project, Tag 00NI](https://stacks.math.columbia.edu/tag/00NI)
* [Stacks Project, Tag 00NJ](https://stacks.math.columbia.edu/tag/00NJ)
* [Stacks Project, Tag 00NL](https://stacks.math.columbia.edu/tag/00NL)
* [Stacks Project, Tag 02I1](https://stacks.math.columbia.edu/tag/02I1)
* [Stacks Project, Tag 02IH](https://stacks.math.columbia.edu/tag/02IH)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace IrreducibleClosedsCodim

end IrreducibleClosedsCodim

namespace Catenary

/-- A space that is catenary in the codimension sense has catenary poset of irreducible closed
subsets: `topCodim Y Y'` bounds every chain, and every maximal chain has length `topCodim Y Y'`,
so any two of them agree. -/
theorem AlgebraicGeometry.catenaryOrder_of_catenarySpace {X : Type*} [TopologicalSpace X]
    (hX : IrreducibleClosedsCodim.IsCatenarySpace X) :
    IsCatenaryOrder (IrreducibleCloseds X) := by
  intro Y Z hYZ
  obtain ⟨hfin, heq⟩ := hX Y Z hYZ
  refine ⟨⟨(IrreducibleClosedsCodim.topCodim Y Z).toNat, ?_⟩, ?_⟩
  · intro s hs ht
    have h := IrreducibleClosedsCodim.length_le_topCodim Y Z s hs ht
    rw [← ENat.natCast_toNat hfin] at h
    exact_mod_cast h
  · intro s t hs ht hs' ht'
    let s' : LTSeries (IrreducibleCloseds X) := ⟨s.length, s.toFun, fun i => (s.step i).lt⟩
    let t' : LTSeries (IrreducibleCloseds X) := ⟨t.length, t.toFun, fun i => (t.step i).lt⟩
    exact_mod_cast (heq s' ⟨hs, ht, s.step⟩).trans (heq t' ⟨hs', ht', t.step⟩).symm

end Catenary

namespace Ring

/-- A catenary ring has catenary poset of primes: the two conditions differ only in that
`Ring.IsCatenary` presents a saturated chain as an `LTSeries` all of whose steps cover, and
`Catenary.IsCatenaryOrder` presents it as a `RelSeries` for `⋖`. -/
theorem IsCatenary.isCatenaryOrder {R : Type u} [CommRing R] (hR : IsCatenary R) :
    Catenary.IsCatenaryOrder (PrimeSpectrum R) := by
  intro p q hpq
  obtain ⟨hbound, n, hn⟩ := hR p q hpq
  refine ⟨hbound, ?_⟩
  intro s t hs ht hs' ht'
  let s' : LTSeries (PrimeSpectrum R) := ⟨s.length, s.toFun, fun i => (s.step i).lt⟩
  let t' : LTSeries (PrimeSpectrum R) := ⟨t.length, t.toFun, fun i => (t.step i).lt⟩
  exact (hn s' hs ht s.step).trans (hn t' hs' ht' t.step).symm

/-- A commutative ring is catenary (`Ring.IsCatenary`) exactly when its spectrum is a catenary
topological space. This is the content of Stacks 02IH, transported from
`Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum`, which carries that attribute. -/
@[ega "0 16.1.4", ega "IV 5.1.1"]
theorem isCatenary_iff_isCatenarySpace_primeSpectrum {R : Type u} [CommRing R] :
    IsCatenary R ↔ IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R) := by
  refine ⟨fun h => AlgebraicGeometry.catenarySpace_of_order
    ((Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mp h.isCatenaryOrder),
    fun h p q hpq => ?_⟩
  obtain ⟨⟨N, hN⟩, heq⟩ := (Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mpr
    (Catenary.AlgebraicGeometry.catenaryOrder_of_catenarySpace h) p q hpq
  refine ⟨⟨N, hN⟩, ?_⟩
  by_cases hex : ∃ s : LTSeries (PrimeSpectrum R), s.head = p ∧ s.last = q ∧
      ∀ i : Fin s.length, s i.castSucc ⋖ s i.succ
  · obtain ⟨t, htp, htq, htsat⟩ := hex
    exact ⟨t.length, fun s hs ht hsat =>
      heq ⟨s.length, s.toFun, hsat⟩ ⟨t.length, t.toFun, htsat⟩ hs ht htp htq⟩
  · exact ⟨0, fun s hs ht hsat => (hex ⟨s, hs, ht, hsat⟩).elim⟩

/-- The two universal-catenarity predicates agree: both quantify over the finite-type algebras in
the universe of the base ring, and catenarity of such an algebra is catenarity of its
spectrum. -/
theorem isUniversallyCatenary_iff_isUniversallyCatenary {R : Type u} [CommRing R] :
    IsUniversallyCatenary R ↔ _root_.IsUniversallyCatenary R := by
  refine ⟨fun h C _ _ hC => ?_, fun h C _ _ _ =>
    isCatenary_iff_isCatenarySpace_primeSpectrum.mpr (h C ‹Algebra.FiniteType R C›)⟩
  have : Algebra.FiniteType R C := hC
  exact isCatenary_iff_isCatenarySpace_primeSpectrum.mp (h C)

/-- Universal catenarity in the sense of Stacks 00NL is Noetherianity together with the
topological predicate `IsUniversallyCatenary`. -/
theorem isUniversallyCatenaryNoetherian_iff_isNoetherianRing_and_isUniversallyCatenary
    {R : Type u} [CommRing R] :
    IsUniversallyCatenaryNoetherian R ↔ IsNoetherianRing R ∧ _root_.IsUniversallyCatenary R :=
  and_congr_right fun _ => isUniversallyCatenary_iff_isUniversallyCatenary

/-- A localization of a Noetherian universally catenary ring is universally catenary, for the
predicate `Ring.IsUniversallyCatenary`. This is Stacks 00NJ, transported from
`localization_isUniversallyCatenary`, which carries that attribute. -/
@[ega "IV 10.7.2" "more general", ega "IV 5.6.3"]
theorem IsUniversallyCatenary.localization {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : Submonoid A) (R : Type u) [CommRing R] [Algebra A R] [IsLocalization S R]
    (hA : IsUniversallyCatenary A) : IsUniversallyCatenary R :=
  isUniversallyCatenary_iff_isUniversallyCatenary.mpr
    (localization_isUniversallyCatenary A S R
      (isUniversallyCatenary_iff_isUniversallyCatenary.mp hA))

/-- Let `S` be a multiplicative subset of a ring `R` and `A = S⁻¹R`. If `R` is catenary, then so
is `A`; if `R` is Noetherian and universally catenary, then `A` is Noetherian and universally
catenary. -/
@[stacks 00NJ]
theorem isCatenary_and_isUniversallyCatenary_of_isLocalization {R : Type u} [CommRing R]
    (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A] :
    (IsCatenary R → IsCatenary A) ∧
      (IsNoetherianRing R → IsUniversallyCatenary R →
        IsNoetherianRing A ∧ IsUniversallyCatenary A) := by
  refine ⟨AlgebraicGeometry.ringIsCatenary_of_isLocalization S, fun hR hU => ?_⟩
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing S A hR
  exact ⟨this, hU.localization S A⟩

end Ring
