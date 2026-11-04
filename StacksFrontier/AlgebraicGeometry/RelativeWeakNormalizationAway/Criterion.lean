module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeWeakNormalization

/-!
# Recognising a universal homeomorphism of affine spectra from ring data

`AlgebraicGeometry.universalHomeomorphism_iff_integral_universallyInjective_surjective`
characterises universal homeomorphisms by three scheme-theoretic properties. For a morphism of
affine schemes coming from an algebra, all three are ring-theoretic: integrality of the algebra,
uniqueness of field-valued extensions, and nilpotency of the kernel of the structure map. This
file packages that translation, so that a universal homeomorphism of spectra can be produced
from ring data.

## Main results

* `AlgebraicGeometry.specMap_surjective_of_isIntegral_of_ker_le_nilradical`: an integral algebra
  whose structure map has a kernel of nilpotents has surjective spectrum map.
* `AlgebraicGeometry.universalHomeomorphism_specMap_of_isIntegral`: a universal homeomorphism of
  spectra from integrality, uniqueness of field-valued extensions, and a kernel of nilpotents.
* `AlgebraicGeometry.isDominant_specMap_iff_ker_le_nilradical`: dominance of the spectrum map of
  an algebra is nilpotency of the kernel of its structure map.
* `AlgebraicGeometry.ker_algebraMap_subalgebra_le_nilradical`: a subalgebra inherits that
  nilpotency from the ambient algebra.

## Implementation notes

Integrality and the kernel condition are stated for `algebraMap A C`, because every use applies
them to a subalgebra of a fixed ambient ring. The uniqueness statement is stated for a bare ring
map instead, since it is also applied to maps that are not structure maps of an algebra.

## References

* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An integral algebra map whose kernel consists of nilpotents has surjective spectrum map. -/
theorem specMap_surjective_of_isIntegral_of_ker_le_nilradical
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C]
    (hker : RingHom.ker (algebraMap A C) ≤ nilradical A) :
    Function.Surjective (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := by
  change Function.Surjective (PrimeSpectrum.comap (algebraMap A C))
  intro p
  have hp : p.asIdeal.IsPrime := p.2
  have hkerP : RingHom.ker (algebraMap A C) ≤ p.asIdeal :=
    hker.trans (nilradical_le_prime p.asIdeal)
  obtain ⟨q, _, hqprime, hqp⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal C) (by
      intro x hx
      apply hkerP
      simpa [RingHom.mem_ker] using hx)
  exact ⟨⟨q, hqprime⟩, PrimeSpectrum.ext hqp⟩

/-- The spectrum map of an integral algebra whose structure map has nilpotent kernel and admits
unique field-valued extensions is a universal homeomorphism. -/
theorem universalHomeomorphism_specMap_of_isIntegral
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C]
    (hker : RingHom.ker (algebraMap A C) ≤ nilradical A)
    (hunique : ∀ (K : Type u) [Field K] (φ ψ : C →+* K),
      φ.comp (algebraMap A C) = ψ.comp (algebraMap A C) → φ = ψ) :
    UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := by
  have hi : IsIntegralHom (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr ‹Algebra.IsIntegral A C›)
  have hsurj : Surjective (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) :=
    (surjective_iff _).2 (specMap_surjective_of_isIntegral_of_ker_le_nilradical hker)
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
    ⟨hi, universallyInjective_specMap_of_ringHom_unique _ hunique, hsurj⟩

/-- The spectrum map of an algebra is dominant exactly when the kernel of its structure map
consists of nilpotents. -/
theorem isDominant_specMap_iff_ker_le_nilradical
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) ↔
      RingHom.ker (algebraMap A B) ≤ nilradical A := by
  rw [isDominant_iff]
  exact PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap A B)

/-- The structure map of a subalgebra inherits the nilpotency of the kernel of the ambient
structure map. -/
theorem ker_algebraMap_subalgebra_le_nilradical
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (C : Subalgebra A B)
    (hker : RingHom.ker (algebraMap A B) ≤ nilradical A) :
    RingHom.ker (algebraMap A C) ≤ nilradical A := by
  intro a ha
  apply hker
  simpa [RingHom.mem_ker] using congrArg (fun z : C => (z : B)) (RingHom.mem_ker.mp ha)

end AlgebraicGeometry

end
