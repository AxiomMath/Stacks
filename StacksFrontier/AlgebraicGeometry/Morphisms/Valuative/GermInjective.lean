module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.Topology.Irreducible
public import StacksFrontier.RingTheory.Localization.AwayToAtPrime

/-!
# Germ injectivity on reduced schemes with finitely many components

On a reduced scheme with only finitely many irreducible components, every point has an affine
open neighbourhood on which the canonical germ map from sections to the local ring is
injective. Mathlib supplies the same conclusion for integral schemes and for locally
Noetherian schemes; this file covers the remaining case.

## Main results

* `AlgebraicGeometry.Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents`
  establishes `Scheme.IsGermInjective` for a reduced scheme with finitely many irreducible
  components.

## Implementation notes

The affine case is reduced to the spectrum of the ring of global sections, where the
injectivity of a localization away from an element is supplied by
`exists_injective_localizationAwayToAtPrime_of_isReduced_finite_minimalPrimes`; the minimal
primes are matched with the irreducible components of the spectrum. The general case follows
by covering the scheme with affine opens, using that an open embedding cannot increase the
number of irreducible components.

## References

* [Stacks Project, Tag 0BX3](https://stacks.math.columbia.edu/tag/0BX3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An open embedding does not increase the number of irreducible components. -/
lemma finite_irreducibleComponents_of_isOpenEmbedding
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : Y → Z) (hf : Topology.IsOpenEmbedding f)
    (hZ : (irreducibleComponents Z).Finite) :
    (irreducibleComponents Y).Finite := by
  classical
  apply (hZ.image fun C : Set Z ↦ f ⁻¹' C).subset
  intro C hC
  obtain ⟨D, hD, hCD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (f '' C) (hC.1.image f hf.continuous.continuousOn)
  have hsub : C ⊆ f ⁻¹' D := fun y hy ↦ hCD ⟨y, hy, rfl⟩
  obtain ⟨y, hy⟩ := hC.1.1
  exact ⟨D, hD, (Set.Subset.antisymm hsub (hC.2 (preimage_mem_irreducibleComponents
    hD hf ⟨f y, hsub hy, y, rfl⟩).1 hsub)).symm⟩

/-- The spectrum of a reduced ring whose spectrum has finitely many irreducible components is
germ injective. -/
private lemma isGermInjective_Spec_of_isReduced_finite_irreducibleComponents
    (R : CommRingCat.{u}) [_root_.IsReduced R]
    (hR : (irreducibleComponents (PrimeSpectrum R)).Finite) :
    (Spec R).IsGermInjective := by
  apply Scheme.IsGermInjective.Spec
  intro p hp
  have : p.IsPrime := hp
  obtain ⟨f, hf, hinj⟩ :=
    exists_injective_localizationAwayToAtPrime_of_isReduced_finite_minimalPrimes p
      (((Equiv.set_finite_iff
        (minimalPrimes.equivIrreducibleComponents R).toEquiv).mpr hR).subset
          (Set.sep_subset _ _))
  refine ⟨f, hf, ?_⟩
  intro x y hyx hy
  have hxAway : algebraMap R (Localization.Away f) x = 0 := by
    apply hinj
    simpa [localizationAwayToAtPrime] using
      (IsLocalization.map_eq_zero_iff p.primeCompl _ _).2 ⟨⟨y, hy⟩, hyx⟩
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _] at hxAway
  obtain ⟨⟨z, n, rfl⟩, hn⟩ := hxAway
  exact ⟨n, hn⟩

/-- An affine reduced scheme with finitely many irreducible components is germ injective. -/
private lemma isGermInjective_of_isAffine_isReduced_finite_irreducibleComponents
    (Y : Scheme.{u}) [IsAffine Y] [IsReduced Y]
    (hY : (irreducibleComponents Y).Finite) : Y.IsGermInjective := by
  let R := Γ(Y, ⊤)
  have : _root_.IsReduced R := (affine_isReduced_iff R).mp
    (isReduced_of_isOpenImmersion Y.isoSpec.inv)
  have : (Spec R).IsGermInjective :=
    isGermInjective_Spec_of_isReduced_finite_irreducibleComponents R
      (finite_irreducibleComponents_of_isOpenEmbedding Y.isoSpec.inv
        Y.isoSpec.inv.isOpenEmbedding hY)
  intro y
  have : Y.IsGermInjectiveAt (Y.isoSpec.inv (Y.isoSpec.hom y)) := inferInstance
  simpa using this

/-- A reduced scheme with only finitely many irreducible components is germ injective: every
point has an affine open neighbourhood whose ring of sections injects into the local ring at
that point. -/
lemma Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents
    (X : Scheme.{u}) [IsReduced X]
    (hX : (irreducibleComponents X).Finite) : X.IsGermInjective :=
  @Scheme.IsGermInjective.of_openCover _ X.affineCover (fun i ↦ by
    have : IsReduced (X.affineCover.X i) :=
      isReduced_of_isOpenImmersion (X.affineCover.f i)
    exact isGermInjective_of_isAffine_isReduced_finite_irreducibleComponents _
      (finite_irreducibleComponents_of_isOpenEmbedding (X.affineCover.f i)
      (X.affineCover.f i).isOpenEmbedding hX))

end AlgebraicGeometry

end
