module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalIsomorphism

/-!
# Flatness of algebras that identify local rings

An algebra that identifies local rings is flat: flatness of a module over the base can be tested
at the maximal ideals of the algebra, and at each of them the canonical map from the local ring
of the base is an isomorphism. If in addition the induced map of prime spectra is surjective,
the algebra is faithfully flat.

## Main results

* `AlgebraicGeometry.ProEtale.flat_of_identifiesLocalRings`: an algebra identifying local rings
  is flat.
* `AlgebraicGeometry.ProEtale.faithfullyFlat_of_comap_surjective_of_identifiesLocalRings`: it is
  faithfully flat as soon as its map of prime spectra is surjective.

## Implementation notes

Flatness is tested with `Module.flat_of_isLocalized_maximal` applied to the algebra viewed as a
module over itself, localized at its maximal ideals. Identifying local rings makes the canonical
map from the localization of the base at the contracted prime bijective, hence flat, and
flatness over the base then follows by transitivity along that map. Faithful flatness is read off
from the characterization of faithfully flat ring maps as the flat ones with surjective map of
prime spectra. The base and the algebra lie in independent universes: flatness is tested on
modules over the base, which imposes no size relation between the two.

## References

* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u v

/-- An algebra that identifies local rings is flat over its base. -/
theorem flat_of_identifiesLocalRings (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] (h : Algebra.IdentifiesLocalRings R S) : Module.Flat R S := by
  apply Module.flat_of_isLocalized_maximal S S
    (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap S (Localization.AtPrime P))
  intro P hP
  have : P.IsPrime := hP.isPrime
  let p : Ideal R := P.comap (algebraMap R S)
  have : p.IsPrime := Ideal.comap_isPrime (algebraMap R S) P
  let g : Localization.AtPrime p →+* Localization.AtPrime P :=
    Localization.localRingHom p P (algebraMap R S) rfl
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) := g.toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (Localization.localRingHom_to_map p P (algebraMap R S) rfl x).symm
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) :=
    RingHom.Flat.of_bijective (h P)
  exact Module.Flat.trans R (Localization.AtPrime p) (Localization.AtPrime P)

/-- An algebra that identifies local rings and whose map of prime spectra is surjective is
faithfully flat over its base. -/
theorem faithfullyFlat_of_comap_surjective_of_identifiesLocalRings
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.IdentifiesLocalRings R S)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    (algebraMap R S).FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  exact ⟨RingHom.flat_algebraMap_iff.mpr (flat_of_identifiesLocalRings R S h), hsurj⟩

end AlgebraicGeometry.ProEtale

end
