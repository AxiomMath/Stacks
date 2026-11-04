module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange

/-!
# Étaleness over an open of the target, read prime by prime

Two readings of "`Spec B ⟶ Spec A` is étale over an open `U ⊆ Spec A`" are compared here: the
geometric one, étaleness of the restricted morphism `Spec.map φ ∣_ U`, and the pointwise one,
Mathlib's `Algebra.IsEtaleAt A q` at each prime `q` of `B` whose contraction lies in `U`. The
geometric form is what [Stacks, Tag 0BMA] is stated with in this library; the pointwise form is
what a reduction producing the hypothesis one prime at a time has in hand.

The comparison is immediate from two facts already available: étaleness at a point is the étale
locus condition, which is stable under base change along a flat morphism
([Stacks, Tag 0476], `AlgebraicGeometry.etaleAt_iff_of_isPullback`) and the restriction of a
morphism to an open of the target is the base change along the open immersion; and for a finite
type algebra over a Noetherian ring, étaleness of a morphism of spectra at a prime is étaleness
of the local ring map there ([Stacks, Tag 039N] and [Stacks, Tag 039L]).

## Main results

* `AlgebraicGeometry.etale_morphismRestrict_of_forall_etaleAt` — a morphism locally of finite
  presentation which is étale at every point over an open of the target restricts to an étale
  morphism over that open.
* `AlgebraicGeometry.etaleAt_specMap_iff_isEtaleAt` — for a finite type algebra over a
  Noetherian ring, étaleness of the morphism of spectra at a prime is `Algebra.IsEtaleAt`.
* `AlgebraicGeometry.etale_specMap_restrict_puncturedSpectrum_of_isEtaleAt` — the two readings
  compared over the punctured spectrum of a Noetherian local ring.

## References

* [Stacks Project, Tag 0476](https://stacks.math.columbia.edu/tag/0476)
* [Stacks Project, Tag 039L](https://stacks.math.columbia.edu/tag/039L)
* [Stacks Project, Tag 039N](https://stacks.math.columbia.edu/tag/039N)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism locally of finite presentation which is étale at every point lying over an open
subset of the target restricts to an étale morphism over that open. -/
public lemma etale_morphismRestrict_of_forall_etaleAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (U : Y.Opens)
    (h : ∀ x : X, f x ∈ U → EtaleAt f x) :
    Etale (f ∣_ U) :=
  (etale_iff_forall_etaleAt (f ∣_ U)).mpr fun z =>
    (etaleAt_iff_of_isPullback (isPullback_morphismRestrict f U).flip
      (Or.inr inferInstance) z).mp (h ((f ⁻¹ᵁ U).ι z) z.2)

/-- For a finite type algebra over a Noetherian ring, the morphism of spectra is étale at a
prime exactly when the algebra is étale at that prime in the sense of `Algebra.IsEtaleAt`. -/
public lemma etaleAt_specMap_iff_isEtaleAt {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B]
    (q : Ideal B) [hq : q.IsPrime] :
    EtaleAt (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (show ↥(Spec (CommRingCat.of B)) from (⟨q, hq⟩ : PrimeSpectrum B)) ↔
      Algebra.IsEtaleAt A q := by
  have _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  let p : Ideal A := Ideal.comap (algebraMap A B) q
  have _ : p.IsPrime := inferInstanceAs (Ideal.comap (algebraMap A B) q).IsPrime
  have _ : q.LiesOver p := ⟨rfl⟩
  have _ : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have _ : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  rw [← isEtaleAt_iff_etaleAt, Algebra.isEtaleAt_iff_isEtaleLocalHom p q]
  -- Each of the three conditions defining `RingHom.IsEtaleLocalHom` respects isomorphisms of
  -- arrows, and the stalk map is isomorphic to the localized algebra map.
  have e := Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap A B))
    (⟨q, hq⟩ : PrimeSpectrum B)
  exact and_congr (RingHom.Flat.respectsIso.arrow_mk_iso_iff e)
    (and_congr (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff e)
      (RingHom.EssFiniteType.respectsIso.arrow_mk_iso_iff e))

/-- For a finite algebra over a Noetherian local ring, étaleness of the morphism of spectra over
the punctured spectrum follows from `Algebra.IsEtaleAt` at every prime whose contraction is not
the maximal ideal. -/
public lemma etale_specMap_restrict_puncturedSpectrum_of_isEtaleAt
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsNoetherianRing A] [Module.Finite A B]
    (h : ∀ q : Ideal B, ∀ _ : q.IsPrime,
      Ideal.comap (algebraMap A B) q ≠ IsLocalRing.maximalIdeal A → Algebra.IsEtaleAt A q) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_ Stacks.puncturedSpectrum A) := by
  have _ : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have _ : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  refine etale_morphismRestrict_of_forall_etaleAt _ _ fun q hq => ?_
  have _ : q.asIdeal.IsPrime := q.isPrime
  have hpt : (show ↥(Spec (CommRingCat.of B)) from
      (⟨q.asIdeal, q.isPrime⟩ : PrimeSpectrum B)) = q := rfl
  rw [← hpt, etaleAt_specMap_iff_isEtaleAt]
  exact h q.asIdeal q.isPrime fun hcontra =>
    (Stacks.mem_puncturedSpectrum A).mp hq (PrimeSpectrum.ext hcontra)

end AlgebraicGeometry

end
