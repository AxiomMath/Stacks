module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.SurjectiveOnStalks
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteSpectrum
public import StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings
public import StacksFrontier.Topology.Profinite.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Profiniteness of a spectrum goes up along a map identifying local rings

A ring map that identifies local rings induces isomorphisms, hence trivial and in particular
algebraic extensions, of residue fields. Profiniteness of the prime spectrum therefore goes up
along such a map.

## Main results

* `AlgebraicGeometry.ProEtale.residueField_map_bijective_of_identifiesLocalRings`: an algebra
  identifying local rings induces an isomorphism on residue fields at every prime of the
  target.
* `AlgebraicGeometry.ProEtale.isAlgebraic_residueField_of_identifiesLocalRings`: those residue
  field extensions are algebraic.
* `AlgebraicGeometry.ProEtale.isProfiniteStacks_primeSpectrum_of_identifiesLocalRings`:
  profiniteness of the prime spectrum, in the form `IsProfiniteStacks`, goes up along an algebra
  identifying local rings ([Stacks, Tag 0978], part (4)).

## References

* [Stacks Project, Tag 0978](https://stacks.math.columbia.edu/tag/0978)
* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- An algebra identifying local rings has bijective maps of residue fields at every prime of the
target. -/
theorem residueField_map_bijective_of_identifiesLocalRings
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (h : Algebra.IdentifiesLocalRings A B) (q : Ideal B) [q.IsPrime] :
    Function.Bijective
      (Ideal.ResidueField.map (q.comap (algebraMap A B)) q (algebraMap A B) rfl) :=
  RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    (f := algebraMap A B) (fun P _ => (h P).surjective) _ q rfl

/-- An algebra identifying local rings induces algebraic extensions of residue fields. -/
theorem isAlgebraic_residueField_of_identifiesLocalRings
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (h : Algebra.IdentifiesLocalRings A B) (q : Ideal B) [q.IsPrime] :
    letI := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q (algebraMap A B) rfl).toAlgebra
    Algebra.IsAlgebraic (q.comap (algebraMap A B)).ResidueField q.ResidueField := by
  let : Algebra (q.comap (algebraMap A B)).ResidueField q.ResidueField :=
    (Ideal.ResidueField.map (q.comap (algebraMap A B)) q (algebraMap A B) rfl).toAlgebra
  have hbij := residueField_map_bijective_of_identifiesLocalRings h q
  have : Algebra.IsIntegral (q.comap (algebraMap A B)).ResidueField q.ResidueField := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ := (by simpa [RingHom.algebraMap_toAlgebra] using hbij.surjective x :
      ∃ y, algebraMap (q.comap (algebraMap A B)).ResidueField q.ResidueField y = x)
    exact isIntegral_algebraMap
  infer_instance

/-- Profiniteness of the prime spectrum, in the form `IsProfiniteStacks`, goes up along an
algebra identifying local rings ([Stacks, Tag 0978], part (4)). -/
theorem isProfiniteStacks_primeSpectrum_of_identifiesLocalRings
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : Algebra.IdentifiesLocalRings A B)
    (hA : IsProfiniteStacks (PrimeSpectrum A)) :
    IsProfiniteStacks (PrimeSpectrum B) :=
  (isProfiniteStacks_iff_compact_t2_totallyDisconnected _).mpr
    (primeSpectrum_isProfinite_of_identifiesLocalRings A B h
      ((isProfiniteStacks_iff_compact_t2_totallyDisconnected _).mp hA))

end AlgebraicGeometry.ProEtale

end
