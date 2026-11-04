module

public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Etale.Locus
public import StacksFrontier.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale homomorphisms of local rings

A local homomorphism between Noetherian local rings is étale when it is flat and unramified as
a homomorphism of local rings. For a finite type algebra over a Noetherian ring, étaleness at a
prime is exactly this condition on the induced homomorphism of local rings.

## Main definitions

* `RingHom.IsEtaleLocalHom` is the predicate that a local homomorphism of Noetherian local
  rings is étale.

## Main results

* `Algebra.isEtaleAt_iff_isEtaleLocalHom` identifies étaleness of a finite type algebra at a
  prime with étaleness of the induced homomorphism of local rings.

## Implementation notes

For an essentially finite type local algebra, `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`
identifies formal unramifiedness with equality of the extended maximal ideal and the target
maximal ideal together with separability of the residue field extension, and the residue field
extension is automatically finite in this setting. Thus formal unramifiedness together with
essential finite type is precisely the unramifiedness of a homomorphism of local rings used
here. This differs from `RingHom.Etale`, which requires finite presentation rather than merely
essential finite type.

The predicate is an abbreviation, so that the APIs for flatness, formal unramifiedness and
essential finite type apply to it directly. It is stated for ring homomorphisms rather than for
morphisms of schemes, which is where the source places it.

## References

* [Stacks Project, Tag 0258](https://stacks.math.columbia.edu/tag/0258)
* [Stacks Project, Tag 039L](https://stacks.math.columbia.edu/tag/039L)
-/

@[expose] public section

universe u v

namespace RingHom

/-- A local homomorphism between Noetherian local rings is étale if it is flat, formally
unramified, and essentially of finite type. -/
@[stacks 0258, sga "1 I 4.1" "special case", sga "1 III 1.2" "partial"]
abbrev IsEtaleLocalHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] : Prop :=
  f.Flat ∧ f.FormallyUnramified ∧ f.EssFiniteType

end RingHom

namespace Algebra

/-- The induced homomorphism of local rings of an algebra that is étale at a prime is flat. -/
private lemma flat_localRingHom_of_isEtaleAt
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] (h : Algebra.IsEtaleAt A q) :
    (Localization.localRingHom p q (algebraMap A B) Ideal.LiesOver.over).Flat := by
  obtain ⟨g, hg, hge⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) q
  have hle : Submonoid.powers g ≤ q.primeCompl := Submonoid.powers_le.mpr hg
  let : Algebra (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers g)
      q.primeCompl hle
  have : IsScalarTower B (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _
      (Submonoid.powers g) q.primeCompl hle
  have : IsScalarTower A (Localization.Away g) (Localization.AtPrime q) :=
    IsScalarTower.to₁₃₄ _ B _ _
  have : IsLocalization (q.primeCompl.map (algebraMap B (Localization.Away g)))
      (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers g)
      q.primeCompl hle
  have : Module.Flat (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.flat (Localization.AtPrime q)
      (q.primeCompl.map (algebraMap B (Localization.Away g)))
  have : Module.Flat A (Localization.AtPrime q) :=
    let : Algebra.Etale A (Localization.Away g) := hge
    Module.Flat.trans A (Localization.Away g) _
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q)).2 inferInstance
  simpa only [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq] using
    (RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)))

/-- A finite type algebra over a Noetherian ring is étale at a prime if and only if the induced
map between the local rings at the corresponding primes is an étale local homomorphism. -/
@[stacks 039L]
theorem isEtaleAt_iff_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsEtaleAt A q ↔
      letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
      letI : IsNoetherianRing (Localization.AtPrime p) :=
        IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
      letI : IsNoetherianRing (Localization.AtPrime q) :=
        IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
      RingHom.IsEtaleLocalHom
        (Localization.localRingHom p q (algebraMap A B) Ideal.LiesOver.over) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨fun h => ?_, fun ⟨hflat, hunram, _⟩ => ?_⟩
  · have : Algebra.FormallyEtale A (Localization.AtPrime q) := h
    have : Algebra.FormallyEtale (Localization.AtPrime p)
        (Localization.AtPrime q) := Algebra.FormallyEtale.localization_base p.primeCompl
    refine ⟨flat_localRingHom_of_isEtaleAt p q h,
      RingHom.formallyUnramified_algebraMap.mpr inferInstance, ?_⟩
    have : Algebra.EssFiniteType A (Localization.AtPrime q) := inferInstance
    exact RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_comp A _ _)
  · have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
      RingHom.flat_algebraMap_iff.mp hflat
    have : Algebra.FormallyUnramified (Localization.AtPrime p)
        (Localization.AtPrime q) :=
      RingHom.formallyUnramified_algebraMap.mp hunram
    have : Algebra.IsUnramifiedAt A q :=
      Algebra.FormallyUnramified.comp A (Localization.AtPrime p) _
    exact Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal p q
      ((Algebra.isUnramifiedAt_iff_map_eq A p q).mp inferInstance).2

end Algebra
