module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import StacksFrontier.RingTheory.Flat.NormalFibres
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regularity and normality along an étale local homomorphism

An étale homomorphism of Noetherian local rings neither creates nor destroys regularity, and
neither creates nor destroys the property of being a normal domain. Both statements are
equivalences: the source has the property exactly when the target does.

## Main results

* `RingHom.isRegularLocalRing_iff_of_isEtaleLocalHom`: the source of an étale local
  homomorphism is a regular local ring if and only if its target is.
* `RingHom.isNormalDomain_iff_of_isEtaleLocalHom`: the source of an étale local homomorphism
  is a normal domain if and only if its target is.

## Implementation notes

Neither ring is assumed in advance to have the property in question: `IsRegularLocalRing`
already carries the local and Noetherian conditions, and `IsNormalDomain` packages the domain
property together with integral closedness.

In the forward direction one ascends along a flat local homomorphism whose closed fibre has the
property. For regularity the closed fibre of an étale homomorphism is the residue field of the
target, hence a field; for normality the fibre over an arbitrary prime is a finite reduced
algebra over a field, hence a finite product of fields. In the backward direction an étale local
homomorphism is faithfully flat, and both properties descend along faithfully flat local
homomorphisms.

## References

* [Stacks Project, Tag 025L](https://stacks.math.columbia.edu/tag/025L)
* [Stacks Project, Tag 025N](https://stacks.math.columbia.edu/tag/025N)
* [Stacks Project, Tag 025P](https://stacks.math.columbia.edu/tag/025P)
-/

@[expose] public section

universe u v

namespace RingHom

/-- **Stacks Project, Tag 025N.** An étale local homomorphism between Noetherian local rings
preserves and reflects regularity. -/
@[stacks 025N, sga "1 I 9.1"]
theorem isRegularLocalRing_iff_of_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : IsEtaleLocalHom f) :
    IsRegularLocalRing A ↔ IsRegularLocalRing B := by
  let : Algebra A B := f.toAlgebra
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  have : Module.Flat A B := hf.1
  have : Algebra.FormallyUnramified A B := hf.2.1
  have : Algebra.EssFiniteType A B := hf.2.2
  let : Field (ClosedFibre A B) :=
    Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal.toField
  exact ⟨fun hA => _root_.isRegularLocalRing_of_flat_of_closedFibre A B hA inferInstance hf.1,
    fun _ => IsRegularLocalRing.of_flat_of_isLocalHom B⟩

attribute [stacks 025L "Proposition 025N of the section: for an étale homomorphism `A → B` of
Noetherian local rings, `A` is regular if and only if `B` is regular."]
  RingHom.isRegularLocalRing_iff_of_isEtaleLocalHom

/-- The fibre of a formally unramified, essentially finite type algebra over a prime of the
base is a normal ring: it is a finite reduced algebra over a field, hence a finite product of
fields. -/
private theorem isNormalRing_fiber_of_formallyUnramified
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (p : Ideal A) [p.IsPrime] : IsNormalRing (p.Fiber B) := by
  let K := p.ResidueField
  let S := p.Fiber B
  have : Module.Finite K S := Algebra.FormallyUnramified.finite_of_free K S
  have : IsReduced S := Algebra.FormallyUnramified.isReduced_of_field K S
  have : IsArtinianRing S := IsArtinianRing.of_finite K S
  refine IsNormalRing.congr (IsArtinianRing.equivPi S).symm.toRingEquiv
    (isNormalRing_pi fun i => ?_)
  let : Field (S ⧸ i.asIdeal) := Ideal.Quotient.field i.asIdeal
  exact IsNormalRing.of_isIntegrallyClosed _

/-- **Stacks Project, Tag 025P.** An étale local homomorphism between Noetherian local rings
preserves and reflects the property of being a normal domain. -/
@[stacks 025P, sga "1 I 9.5" "(i), Noetherian"]
theorem isNormalDomain_iff_of_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : IsEtaleLocalHom f) :
    IsNormalDomain A ↔ IsNormalDomain B := by
  let : Algebra A B := f.toAlgebra
  have : Module.Flat A B := flat_algebraMap_iff.mp hf.1
  have : Algebra.FormallyUnramified A B := formallyUnramified_algebraMap.mp hf.2.1
  have : Algebra.EssFiniteType A B := essFiniteType_algebraMap.mp hf.2.2
  refine ⟨fun hA => ?_, fun hB => ?_⟩
  · have : IsDomain A := hA.isDomain
    have : IsIntegrallyClosed A := hA.isIntegrallyClosed
    obtain ⟨hd, hc⟩ := (isNormalRing_of_flat_of_isNormalRing_fiber
      (IsNormalRing.of_isIntegrallyClosed A)
      (isNormalRing_fiber_of_formallyUnramified (B := B))).of_isLocalRing
    exact ⟨hd, hc⟩
  · have : IsDomain B := hB.isDomain
    have : IsIntegrallyClosed B := hB.isIntegrallyClosed
    have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    obtain ⟨hd, hc⟩ := (show IsNormalRing A from
      isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat
        (IsNormalRing.of_isIntegrallyClosed B)).of_isLocalRing
    exact ⟨hd, hc⟩

attribute [stacks 025L "Proposition 025P of the section: for an étale homomorphism `A → B` of
Noetherian local rings, `A` is a normal domain if and only if `B` is a normal domain."]
  RingHom.isNormalDomain_iff_of_isEtaleLocalHom

end RingHom
