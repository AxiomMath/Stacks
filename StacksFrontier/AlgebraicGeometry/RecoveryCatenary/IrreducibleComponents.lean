module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.RecoveryCatenary.Local

/-!
# Universal catenarity and irreducible components

A locally Noetherian scheme is universally catenary precisely when each of its irreducible
components, with the reduced induced scheme structure, is universally catenary. The scheme
structure on a component is the reduced closed subscheme cut out by its vanishing ideal.

## Main results

* `AlgebraicGeometry.Scheme.isUniversallyCatenary_iff_irreducibleComponents`: a locally
  Noetherian scheme is universally catenary if and only if its reduced irreducible components are.

## References

* [Stacks Project, Tag 0G42](https://stacks.math.columbia.edu/tag/0G42)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IrreducibleClosedsCodim

namespace AlgebraicGeometry.Scheme

universe u

/-- Every minimal prime of the ring of sections over an affine open is cut out by the
vanishing ideal of some irreducible component of the scheme. -/
private lemma exists_irreducibleComponent_ideal_eq_minimalPrime
    (S : Scheme.{u}) [IsLocallyNoetherian S] (U : S.affineOpens)
    (p : Ideal Γ(S, U)) (hp : p ∈ minimalPrimes Γ(S, U)) :
    ∃ Z : irreducibleComponents S,
      (Scheme.IdealSheafData.vanishingIdeal
        ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).ideal U = p := by
  let x : PrimeSpectrum Γ(S, U) := ⟨p, hp.1.1⟩
  have hxcomp : closure ({x} : Set (PrimeSpectrum Γ(S, U))) ∈
      irreducibleComponents (PrimeSpectrum Γ(S, U)) :=
    PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mp (by simpa [x] using hp)
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  let f : PrimeSpectrum Γ(S, U) → S := fun y => U.2.fromSpec y
  have hf : Topology.IsOpenEmbedding f := U.2.fromSpec.isOpenEmbedding
  obtain ⟨Z, hZ, hxZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({f x} : Set S) isIrreducible_singleton
  have hprecomp : f ⁻¹' Z ∈ irreducibleComponents (PrimeSpectrum Γ(S, U)) :=
    preimage_mem_irreducibleComponents hZ hf ⟨f x, hxZ (Set.mem_singleton _), x, rfl⟩
  have hpreclosed : IsClosed (f ⁻¹' Z) :=
    (isClosed_of_mem_irreducibleComponents Z hZ).preimage hf.continuous
  have hsub : closure ({x} : Set (PrimeSpectrum Γ(S, U))) ⊆ f ⁻¹' Z :=
    closure_minimal (Set.singleton_subset_iff.mpr (hxZ (Set.mem_singleton _))) hpreclosed
  have hset : f ⁻¹' Z = closure ({x} : Set (PrimeSpectrum Γ(S, U))) :=
    (Set.Subset.antisymm hsub (hxcomp.2 hprecomp.1 hsub)).symm
  refine ⟨⟨Z, hZ⟩, ?_⟩
  change PrimeSpectrum.vanishingIdeal (f ⁻¹' Z) = p
  rw [hset, PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]

/-- The two formulations of catenarity of a ring agree: chains of primes with bounded length
and equilong non-refinable chains, or the same condition phrased with `PrimeChain`. -/
private lemma ringIsCatenary_iff_isCatenaryRing (R : Type u) [CommRing R] :
    Ring.IsCatenary R ↔ _root_.IsCatenaryRing R := by
  classical
  constructor
  · intro h p q hpq
    obtain ⟨⟨N, hN⟩, n, hn⟩ := h p q hpq
    refine ⟨⟨N, fun c => hN c.series c.head_eq c.last_eq⟩, ?_⟩
    intro c d hc hd
    exact (hn c.series c.head_eq c.last_eq hc).trans
      (hn d.series d.head_eq d.last_eq hd).symm
  · intro h p q hpq
    obtain ⟨⟨N, hN⟩, heq⟩ := h p q hpq
    refine ⟨⟨N, fun s hs ht => hN ⟨s, hs, ht⟩⟩, ?_⟩
    by_cases hex : ∃ c : PrimeChain R p q, c.IsMaximal
    · obtain ⟨c, hc⟩ := hex
      exact ⟨c.length, fun s hs ht hsat => heq ⟨s, hs, ht⟩ c hsat hc⟩
    · exact ⟨0, fun s hs ht hsat => (hex ⟨⟨s, hs, ht⟩, hsat⟩).elim⟩

/-- For a Noetherian ring the two formulations of universal catenarity agree. -/
private lemma ringIsUniversallyCatenary_iff_isUniversallyCatenaryRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Ring.IsUniversallyCatenary R ↔ IsUniversallyCatenaryRing R :=
  ⟨fun h A _ _ _ => (ringIsCatenary_iff_isCatenaryRing A).mp (h A),
    fun h A _ _ hA => (ringIsCatenary_iff_isCatenaryRing A).mpr (h A hA)⟩

/-- A locally Noetherian scheme is universally catenary if and only if its reduced
irreducible components are universally catenary. -/
@[stacks 0G42]
theorem isUniversallyCatenary_iff_irreducibleComponents
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IsUniversallyCatenary S ↔
      ∀ Z : irreducibleComponents S,
        let I : S.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
        let : IsLocallyNoetherian I.subscheme :=
          LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
        IsUniversallyCatenary I.subscheme := by
  constructor
  · intro hS Z
    exact isUniversallyCatenary_of_locallyOfFiniteType (Scheme.IdealSheafData.subschemeι _) hS
  · intro hcomp
    classical
    apply (isUniversallyCatenary_iff_forall_affineOpens S).mpr
    intro U
    have hnoeth : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian U
    have hquot : ∀ p ∈ minimalPrimes Γ(S, U),
        Ring.IsUniversallyCatenary (Γ(S, U) ⧸ p) := by
      intro p hp
      obtain ⟨Z, hZideal⟩ := exists_irreducibleComponent_ideal_eq_minimalPrime S U p hp
      let I : S.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
        ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
      have hLN : IsLocallyNoetherian I.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
      have hVring : Ring.IsUniversallyCatenary Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) :=
        (isUniversallyCatenary_iff_forall_affineOpens I.subscheme).mp (hcomp Z)
          ⟨_, U.2.preimage I.subschemeι⟩
      have hquotI : Ring.IsUniversallyCatenary (Γ(S, U) ⧸ I.ideal U) :=
        Ring.IsUniversallyCatenary.of_surjective
          (I.subschemeObjIso U).commRingCatIsoToRingEquiv.surjective hVring
      rwa [hZideal] at hquotI
    apply (ringIsUniversallyCatenary_iff_isUniversallyCatenaryRing Γ(S, U)).mpr
    apply (isUniversallyCatenaryRing_iff_quotient_minimalPrimes Γ(S, U)).2
    intro p hp
    exact (ringIsUniversallyCatenary_iff_isUniversallyCatenaryRing _).mp (hquot p hp)

end AlgebraicGeometry.Scheme
