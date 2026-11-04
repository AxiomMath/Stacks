module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.RingTheory.FiniteType.Pi

/-!
# Finite products of ring maps

The map from a ring into a finite product of algebras over it inherits finiteness and
flatness properties from its components. These are the ring-level statements behind descent
along a standard fppf covering, whose total space is the product of the coordinate rings of
the covering members.

## Main results

* `RingHom.FaithfullyFlat.pi`: a finite family of flat maps whose spectra jointly cover the
  spectrum of the source has faithfully flat product map.
* `RingHom.FinitePresentation.pi`: a finite family of maps of finite presentation has a
  product map of finite presentation.

The finite-type statements `Algebra.FiniteType.pi` and `RingHom.FiniteType.pi` complete the
same list; they live in `StacksFrontier.RingTheory.FiniteType.Pi`, which this file imports, so
they are available to every consumer of this one.

## Implementation notes

The index type is only assumed `Finite`; a `Fintype` instance is produced where the proofs
need to sum over it. Flatness of the product is obtained from flatness of the direct sum
through the equivalence of the two for a finite index type, and surjectivity on spectra is
checked by composing with the evaluation maps.

## References

* [Stacks Project, Tag 06NB](https://stacks.math.columbia.edu/tag/06NB)
-/

@[expose] public section

universe u v

namespace RingHom.FaithfullyFlat

/-- A finite family of flat ring maps out of `R` whose spectra jointly cover `Spec R` has a
faithfully flat product map. -/
theorem pi {I : Type v} {R : Type u} [CommRing R] [_root_.Finite I]
    {S : I → Type u} [∀ i, CommRing (S i)] (f : ∀ i, R →+* S i)
    (hflat : ∀ i, (f i).Flat)
    (hsurj : ∀ p : PrimeSpectrum R, ∃ i q, PrimeSpectrum.comap (f i) q = p) :
    (RingHom.pi f).FaithfullyFlat := by
  classical
  have hpi : (RingHom.pi f).Flat := by
    algebraize [RingHom.pi f]
    let _ : ∀ i, Algebra R (S i) := fun i => (f i).toAlgebra
    let _ : Fintype I := Fintype.ofFinite I
    have : Module.Flat R (DirectSum I S) :=
      Module.Flat.directSum_iff.mpr fun i => RingHom.flat_algebraMap_iff.mp (hflat i)
    exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R I S).symm
  refine RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hpi, fun p => ?_⟩
  obtain ⟨i, q, hq⟩ := hsurj p
  exact ⟨PrimeSpectrum.comap (Pi.evalRingHom S i) q, hq⟩

end RingHom.FaithfullyFlat

namespace RingHom.FinitePresentation

/-- A finite family of ring maps of finite presentation out of `R` has a product map of
finite presentation. -/
theorem pi {R : Type*} [CommRing R] {I : Type*} [_root_.Finite I]
    {S : I → Type*} [∀ i, CommRing (S i)] (f : ∀ i, R →+* S i)
    (hf : ∀ i, (f i).FinitePresentation) : (RingHom.pi f).FinitePresentation := by
  let _ : ∀ i, Algebra R (S i) := fun i => (f i).toAlgebra
  have : ∀ i, Algebra.FinitePresentation R (S i) := fun i =>
    RingHom.finitePresentation_algebraMap.mp (hf i)
  let _ : Algebra R (∀ i, S i) := (RingHom.pi f).toAlgebra
  exact RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.pi _)

end RingHom.FinitePresentation
