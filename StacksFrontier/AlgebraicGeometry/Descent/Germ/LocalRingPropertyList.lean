module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.LocalRingProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport
public import StacksFrontier.RingTheory.Etale.LocalRingPropertyList
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale-local properties of germs given by properties of their local rings

`AlgebraicGeometry.GermOfScheme.isEtaleLocal_stalk_property` turns a property of local rings
which is insensitive to étale extension and invariant under isomorphism into an étale-local
property of germs of schemes. This file discharges it once for each property on the source's
list: Noetherian, dimension `d`, regular, discrete valuation ring, reduced, normal, Noetherian
of depth `k`, Noetherian and Cohen-Macaulay, Noetherian and Gorenstein.

## Main results

* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_isNoetherianRing_stalk`
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_ringKrullDim_eq_stalk`
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_isRegularLocalRing_stalk`
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_isDiscreteValuationRing_stalk`
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_isReduced_stalk`
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_isNormalDomain_stalk`
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_isNoetherianRing_and_ringDepth_eq_stalk`
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_isCohenMacaulayLocalRing_stalk`
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_isGorensteinLocalRing_stalk`

## Implementation notes

Each proof supplies the criterion with two hypotheses. The first, insensitivity to étale
extension, is the corresponding statement of
`StacksFrontier.RingTheory.Etale.LocalRingPropertyList`. The second, invariance under an
isomorphism of local rings, is needed because a stalk is only canonically isomorphic to the
localization of a ring of sections; it is `IsRegularLocalRing.of_ringEquiv` for regularity,
`IsNormalRing.congr` for normality, `ringDepth_eq_of_ringEquiv` for depth,
`isCohenMacaulayLocalRing_iff_of_ringEquiv` for Cohen-Macaulayness and
`Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff` for Gorensteinness.

A property of local rings is passed to the criterion as a predicate on commutative rings, so a
property whose very statement needs the local-ring instance — depth, Cohen-Macaulayness,
Gorensteinness — is given to it with that instance bound existentially. The stalk of a scheme
is a local ring, so the bound instance can be discharged afterwards and the statements below
are the direct ones; `isEtaleLocal_of_exists_isLocalRing` performs that step. Noetherianity,
which a property may also presuppose without the ring being local, stays existentially bound
in the two statements that need it to be stated at all.

## References

* [Stacks Project, Tag 0BBL](https://stacks.math.columbia.edu/tag/0BBL)
* [Stacks Project, Tag 04N1](https://stacks.math.columbia.edu/tag/04N1)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

namespace GermOfScheme

/-- Noetherianity depends only on the isomorphism class of a ring. -/
private theorem isNoetherianRing_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IsNoetherianRing R ↔ IsNoetherianRing S :=
  ⟨fun _ => isNoetherianRing_of_ringEquiv R e, fun _ => isNoetherianRing_of_ringEquiv S e.symm⟩

/-- Regularity depends only on the isomorphism class of a local ring. -/
private theorem isRegularLocalRing_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    IsRegularLocalRing R ↔ IsRegularLocalRing S :=
  ⟨fun _ => IsRegularLocalRing.of_ringEquiv e, fun _ => IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- Normality of a local domain transfers along a ring isomorphism. -/
private theorem isNormalDomain_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing S] (e : R ≃+* S) [h : IsNormalDomain R] : IsNormalDomain S := by
  let := h.isDomain
  let := h.isIntegrallyClosed
  obtain ⟨hd, hc⟩ := (IsNormalRing.congr e (IsNormalRing.of_isIntegrallyClosed R)).of_isLocalRing
  exact ⟨hd, hc⟩

/-- Having a Noetherian local ring is an étale-local property of germs of schemes. -/
theorem isEtaleLocal_isNoetherianRing_stalk :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      IsNoetherianRing (g.scheme.presheaf.stalk g.point)) := by
  refine isEtaleLocal_stalk_property
    (fun (R : Type u) => fun [CommRing R] => IsNoetherianRing R) ?_ ?_
  · intro A B _ _ _ _ p _ q _ hq
    exact isNoetherianRing_localizationAtPrime_iff_of_etale p q hq
  · intro R S _ _ _ _ e
    exact isNoetherianRing_iff_of_ringEquiv e

/-- Having a local ring of dimension `d` is an étale-local property of germs of schemes. -/
theorem isEtaleLocal_ringKrullDim_eq_stalk (d : WithBot ℕ∞) :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      ringKrullDim (g.scheme.presheaf.stalk g.point) = d) := by
  refine isEtaleLocal_stalk_property
    (fun (R : Type u) => fun [CommRing R] => ringKrullDim R = d) ?_ ?_
  · intro A B _ _ _ _ p _ q _ hq
    exact ringKrullDim_eq_localizationAtPrime_iff_of_etale p q d hq
  · intro R S _ _ _ _ e
    rw [ringKrullDim_eq_of_ringEquiv e]

/-- Having a regular local ring is an étale-local property of germs of schemes. -/
theorem isEtaleLocal_isRegularLocalRing_stalk :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      IsRegularLocalRing (g.scheme.presheaf.stalk g.point)) := by
  refine isEtaleLocal_stalk_property
    (fun (R : Type u) => fun [CommRing R] => IsRegularLocalRing R) ?_ ?_
  · intro A B _ _ _ _ p _ q _ hq
    exact isRegularLocalRing_localizationAtPrime_iff_of_etale p q hq
  · intro R S _ _ _ _ e
    exact isRegularLocalRing_iff_of_ringEquiv e

/-- Having a discrete valuation ring as local ring is an étale-local property of germs of
schemes. -/
theorem isEtaleLocal_isDiscreteValuationRing_stalk :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      ∃ _ : IsDomain (g.scheme.presheaf.stalk g.point),
        IsDiscreteValuationRing (g.scheme.presheaf.stalk g.point)) := by
  refine isEtaleLocal_stalk_property
    (fun (R : Type u) => fun [CommRing R] => ∃ _ : IsDomain R, IsDiscreteValuationRing R) ?_ ?_
  · intro A B _ _ _ _ p _ q _ hq
    exact isDiscreteValuationRing_localizationAtPrime_iff_of_etale p q hq
  · intro R S _ _ _ _ e
    have hR := (isDiscreteValuationRing_tfae R).out 1 3
    have hS := (isDiscreteValuationRing_tfae S).out 1 3
    rw [hR, hS, isRegularLocalRing_iff_of_ringEquiv e, ringKrullDim_eq_of_ringEquiv e]

/-- Having a reduced local ring is an étale-local property of germs of schemes. -/
@[ega "IV 11.3.13" "special case"]
theorem isEtaleLocal_isReduced_stalk :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      _root_.IsReduced (g.scheme.presheaf.stalk g.point)) := by
  refine isEtaleLocal_stalk_property
    (fun (R : Type u) => fun [CommRing R] => _root_.IsReduced R) ?_ ?_
  · intro A B _ _ _ _ p _ q _ hq
    exact isReduced_localizationAtPrime_iff_of_etale p q hq
  · intro R S _ _ _ _ e
    exact ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
      fun _ => isReduced_of_injective e e.injective⟩

/-- Having a normal local ring is an étale-local property of germs of schemes. -/
theorem isEtaleLocal_isNormalDomain_stalk :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      IsNormalDomain (g.scheme.presheaf.stalk g.point)) := by
  refine isEtaleLocal_stalk_property
    (fun (R : Type u) => fun [CommRing R] => IsNormalDomain R) ?_ ?_
  · intro A B _ _ _ _ p _ q _ hq
    exact isNormalDomain_localizationAtPrime_iff_of_etale p q hq
  · intro R S _ _ _ _ e
    exact ⟨fun _ => isNormalDomain_of_ringEquiv e, fun _ => isNormalDomain_of_ringEquiv e.symm⟩

/-- A property of germs whose statement uses the local-ring instance of the stalk is étale
local as soon as it is so with that instance bound existentially: the stalk of a scheme is a
local ring, and `IsLocalRing` is a `Prop`, so the two readings agree. -/
private theorem isEtaleLocal_of_exists_isLocalRing
    (Φ : (R : Type u) → [CommRing R] → [IsLocalRing R] → Prop)
    (h : IsEtaleLocal (fun g : GermOfScheme.{u} =>
      ∃ hl : IsLocalRing (g.scheme.presheaf.stalk g.point),
        @Φ (g.scheme.presheaf.stalk g.point) _ hl)) :
    IsEtaleLocal (fun g : GermOfScheme.{u} => Φ (g.scheme.presheaf.stalk g.point)) := by
  have hstrip : ∀ g : GermOfScheme.{u},
      (∃ hl : IsLocalRing (g.scheme.presheaf.stalk g.point),
        @Φ (g.scheme.presheaf.stalk g.point) _ hl) ↔
        Φ (g.scheme.presheaf.stalk g.point) :=
    fun _ => ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨inferInstance, hh⟩⟩
  intro X S f hf
  exact (hstrip S).symm.trans ((h f hf).trans (hstrip X))

/-- Having a Noetherian local ring of depth `k` is an étale-local property of germs of
schemes. -/
theorem isEtaleLocal_isNoetherianRing_and_ringDepth_eq_stalk (k : ℕ∞) :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      IsNoetherianRing (g.scheme.presheaf.stalk g.point) ∧
        ringDepth (g.scheme.presheaf.stalk g.point) = k) := by
  refine isEtaleLocal_of_exists_isLocalRing
    (fun (R : Type u) => fun [CommRing R] => fun [hl : IsLocalRing R] =>
      IsNoetherianRing R ∧ @ringDepth R _ hl = k) ?_
  refine isEtaleLocal_stalk_property
    (fun (R : Type u) => fun [CommRing R] =>
      ∃ hl : IsLocalRing R, IsNoetherianRing R ∧ @ringDepth R _ hl = k) ?_ ?_
  · intro A B _ _ _ _ p _ q _ hq
    have h := isNoetherianRing_and_ringDepth_eq_localizationAtPrime_iff_of_etale p q k hq
    exact ⟨fun ⟨_, hh⟩ => ⟨inferInstance, h.mp hh⟩, fun ⟨_, hh⟩ => ⟨inferInstance, h.mpr hh⟩⟩
  · intro R S _ _ _ _ e
    constructor
    · rintro ⟨_, hN, hd⟩
      exact ⟨inferInstance, (isNoetherianRing_iff_of_ringEquiv e).mp hN,
        (ringDepth_eq_of_ringEquiv e).symm.trans hd⟩
    · rintro ⟨_, hN, hd⟩
      exact ⟨inferInstance, (isNoetherianRing_iff_of_ringEquiv e).mpr hN,
        (ringDepth_eq_of_ringEquiv e).trans hd⟩

/-- A property of Noetherian local rings, bound existentially to the Noetherian instance, is an
étale-local property of germs as soon as it is insensitive to étale extension and isomorphism
invariant. -/
private theorem isEtaleLocal_exists_isNoetherianRing_stalk
    (Φ : (R : Type u) → [CommRing R] → [IsNoetherianRing R] → [IsLocalRing R] → Prop)
    (hétale : ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
      (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime], q.comap (algebraMap A B) = p →
        ((∃ h : IsNoetherianRing (Localization.AtPrime p), @Φ _ _ h _) ↔
          ∃ h : IsNoetherianRing (Localization.AtPrime q), @Φ _ _ h _))
    (hiso : ∀ {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
      [IsLocalRing R] [IsLocalRing S], (R ≃+* S) → (Φ R ↔ Φ S)) :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      ∃ hn : IsNoetherianRing (g.scheme.presheaf.stalk g.point),
        @Φ (g.scheme.presheaf.stalk g.point) _ hn _) := by
  refine isEtaleLocal_of_exists_isLocalRing
    (fun (R : Type u) => fun [CommRing R] => fun [hl : IsLocalRing R] =>
      ∃ hn : IsNoetherianRing R, @Φ R _ hn hl) ?_
  refine isEtaleLocal_stalk_property
    (fun (R : Type u) => fun [CommRing R] => ∃ hl : IsLocalRing R,
      ∃ hn : IsNoetherianRing R, @Φ R _ hn hl) ?_ ?_
  · intro A B _ _ _ _ p _ q _ hq
    exact ⟨fun ⟨_, h⟩ => ⟨inferInstance, (hétale p q hq).mp h⟩,
      fun ⟨_, h⟩ => ⟨inferInstance, (hétale p q hq).mpr h⟩⟩
  · intro R S _ _ _ _ e
    constructor
    · rintro ⟨_, hN, h⟩
      let := (isNoetherianRing_iff_of_ringEquiv e).mp hN
      exact ⟨inferInstance, inferInstance, (hiso e).mp h⟩
    · rintro ⟨_, hN, h⟩
      let := (isNoetherianRing_iff_of_ringEquiv e).mpr hN
      exact ⟨inferInstance, inferInstance, (hiso e).mpr h⟩

/-- Having a Noetherian Cohen-Macaulay local ring is an étale-local property of germs of
schemes. -/
@[ega "IV 6.3.5" "special case"]
theorem isEtaleLocal_isCohenMacaulayLocalRing_stalk :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      ∃ hn : IsNoetherianRing (g.scheme.presheaf.stalk g.point),
        @IsCohenMacaulayLocalRing (g.scheme.presheaf.stalk g.point) _ hn _) :=
  isEtaleLocal_exists_isNoetherianRing_stalk
    (fun (R : Type u) => fun [CommRing R] [IsNoetherianRing R] [IsLocalRing R] =>
      IsCohenMacaulayLocalRing R)
    isCohenMacaulayLocalRing_localizationAtPrime_iff_of_etale
    isCohenMacaulayLocalRing_iff_of_ringEquiv

/-- Having a Noetherian Gorenstein local ring is an étale-local property of germs of
schemes. -/
theorem isEtaleLocal_isGorensteinLocalRing_stalk :
    IsEtaleLocal (fun g : GermOfScheme.{u} =>
      ∃ hn : IsNoetherianRing (g.scheme.presheaf.stalk g.point),
        @Dualizing.IsGorensteinLocalRing (g.scheme.presheaf.stalk g.point) _ hn _) :=
  isEtaleLocal_exists_isNoetherianRing_stalk
    (fun (R : Type u) => fun [CommRing R] [IsNoetherianRing R] [IsLocalRing R] =>
      Dualizing.IsGorensteinLocalRing R)
    isGorensteinLocalRing_localizationAtPrime_iff_of_etale
    Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff

end GermOfScheme

end AlgebraicGeometry

end
