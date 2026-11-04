module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein

/-!
# Gorensteinness under étale local homomorphisms

An étale local homomorphism of Noetherian local rings preserves and reflects the Gorenstein
property.

## Main results

* `RingHom.isGorensteinLocalRing_iff_of_isEtaleLocalHom`: the source of an étale local
  homomorphism is Gorenstein if and only if its target is.

## References

* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
* [Stacks Project, Tag 00U4](https://stacks.math.columbia.edu/tag/00U4)
* [Stacks Project, Tag 0E13](https://stacks.math.columbia.edu/tag/0E13)
-/

@[expose] public section

universe u v

namespace RingHom

/-- Gorensteinness is preserved and reflected by an étale local homomorphism of Noetherian
local rings. -/
theorem isGorensteinLocalRing_iff_of_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : IsEtaleLocalHom f) :
    Dualizing.IsGorensteinLocalRing A ↔ Dualizing.IsGorensteinLocalRing B := by
  let : Algebra A B := f.toAlgebra
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hf.1
  have : Algebra.FormallyUnramified A B := RingHom.formallyUnramified_algebraMap.mp hf.2.1
  have : Algebra.EssFiniteType A B := RingHom.essFiniteType_algebraMap.mp hf.2.2
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom f)
  let I := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  have : Nontrivial (B ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
  have hfield : IsField (B ⧸ I) := Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal
  have : IsRegularLocalRing (B ⧸ I) := by
    rw [isRegularLocalRing_iff, IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield,
      ringKrullDim_eq_zero_of_isField hfield]
    simp
  have hcrit := Dualizing.isGorensteinLocalRing_iff_of_flat A B
  exact ⟨fun hA => hcrit.mpr ⟨hA, Dualizing.IsRegularLocalRing.isGorensteinLocalRing _⟩,
    fun hB => (hcrit.mp hB).1⟩

end RingHom
