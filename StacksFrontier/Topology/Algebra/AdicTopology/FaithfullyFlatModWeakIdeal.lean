module

public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.Topology.Algebra.AdicTopology.Completion
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.RingTheory.Flat.QuotientMap

/-!
# Faithful flatness over a weakly admissible ring, tested modulo a weak ideal of definition

Let `B` be a weakly admissible topological ring and let `f : B →+* A` be a flat ring map.  For a
weak ideal of definition `J` of `B`, `f` is faithfully flat exactly when the induced map
`B ⧸ J → A ⧸ JA` is; it suffices to test this on one weak ideal of definition, and it then holds
for all of them.

## Main results

* `RingHom.faithfullyFlat_quotientMap`: faithful flatness passes to `B ⧸ J → A ⧸ JA`, for an
  arbitrary ideal `J`.
* `RingHom.faithfullyFlat_iff_quotientMap`: for a flat ring map and an ideal `J` contained in the
  Jacobson radical, the converse holds.
* `TopologicalRing.le_ringJacobson_of_isWeakIdealOfDefinition`: a weak ideal of definition of a
  weakly admissible topological ring lies in the Jacobson radical.
* `TopologicalRing.faithfullyFlat_tfae_weakIdealOfDefinition`: a flat ring map out of a weakly
  admissible topological ring is faithfully flat if and only if its reduction modulo every, or
  equivalently some, weak ideal of definition is.

## References

* [Stacks Project, Tag 00HQ](https://stacks.math.columbia.edu/tag/00HQ)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0DCZ](https://stacks.math.columbia.edu/tag/0DCZ)
-/

@[expose] public section

open PrimeSpectrum

universe u v

namespace PrimeSpectrum

/-- A point of `Spec R` whose prime contains `I` comes from a point of `Spec (R ⧸ I)`. -/
public theorem mem_range_comap_quotientMk {R : Type*} [CommRing R] {I : Ideal R}
    {x : PrimeSpectrum R} (h : I ≤ x.asIdeal) :
    x ∈ Set.range (comap (Ideal.Quotient.mk I)) := by
  rwa [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, mem_zeroLocus]

/-- The square formed by `f : B →+* A` and the induced map `B ⧸ J → A ⧸ JA` with the two
quotient maps commutes, read on prime spectra. -/
public theorem comap_quotientMap_comap_mk {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    (f : B →+* A) (J : Ideal B) (z : PrimeSpectrum (A ⧸ J.map f)) :
    comap (Ideal.Quotient.mk J)
        (comap (Ideal.quotientMap (J.map f) f Ideal.le_comap_map) z) =
      comap f (comap (Ideal.Quotient.mk (J.map f)) z) := by
  rw [← comap_comp_apply, ← comap_comp_apply, Ideal.quotientMap_comp_mk]

end PrimeSpectrum

namespace RingHom

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A]

/-- If `f : B →+* A` is faithfully flat, so is the induced map `B ⧸ J → A ⧸ JA`, for every ideal
`J` of `B`. -/
public theorem faithfullyFlat_quotientMap (f : B →+* A) (hff : f.FaithfullyFlat) (J : Ideal B) :
    (Ideal.quotientMap (J.map f) f Ideal.le_comap_map).FaithfullyFlat := by
  obtain ⟨hf, hsurj⟩ := RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff
  refine RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
    ⟨flat_quotientMap f hf J, fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := hsurj (comap (Ideal.Quotient.mk J) x)
  have hJy : J.map f ≤ y.asIdeal := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    rw [← comap_asIdeal, hy, comap_asIdeal]
    exact Ideal.mk_ker.ge.trans (Ideal.ker_le_comap _)
  obtain ⟨z, hz⟩ := mem_range_comap_quotientMk hJy
  exact ⟨z, comap_injective_of_surjective _ Ideal.Quotient.mk_surjective <| by
    rw [comap_quotientMap_comap_mk, hz, hy]⟩

/-- For a flat ring map `f : B →+* A` and an ideal `J` of `B` contained in the Jacobson radical,
`f` is faithfully flat if and only if the induced map `B ⧸ J → A ⧸ JA` is faithfully flat. -/
public theorem faithfullyFlat_iff_quotientMap (f : B →+* A) (hf : f.Flat) (J : Ideal B)
    (hJ : J ≤ Ring.jacobson B) :
    f.FaithfullyFlat ↔
      (Ideal.quotientMap (J.map f) f Ideal.le_comap_map).FaithfullyFlat := by
  refine ⟨fun hff ↦ faithfullyFlat_quotientMap f hff J, fun hff ↦ ?_⟩
  obtain ⟨-, hsurj⟩ := RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff
  refine ((faithfullyFlat_tfae00HQ f hf).out 3 1).mp fun x hx ↦ ?_
  have : x.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal x).mp hx
  obtain ⟨w, hw⟩ :=
    mem_range_comap_quotientMk (hJ.trans (Ring.jacobson_le_of_isMaximal x.asIdeal))
  obtain ⟨z, hz⟩ := hsurj w
  exact ⟨comap (Ideal.Quotient.mk (J.map f)) z, by
    rw [← comap_quotientMap_comap_mk, hz, hw]⟩

end RingHom

namespace TopologicalRing

/-- A weak ideal of definition of a weakly admissible topological ring lies in the Jacobson
radical of the ring. -/
@[ega "IV 18.5.7" "special case"]
public theorem le_ringJacobson_of_isWeakIdealOfDefinition {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (hB : TopologicalRing.IsWeaklyAdmissible B) {J : Ideal B}
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) :
    J ≤ Ring.jacobson B :=
  Ideal.jacobson_bot (R := B) ▸
    (TopologicalRing.henselianPair_of_isWeaklyAdmissible B hB J hJ).le_jacobson

/-- The ring map `B ⧸ J → A ⧸ JA` induced by `f : B →+* A` and a weak ideal of definition `J` of
`B`. -/
public abbrev quotientMapOfWeakIdeal {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    B ⧸ J.1 →+* A ⧸ extendedIdeal f J :=
  Ideal.quotientMap (extendedIdeal f J) f Ideal.le_comap_map

/-- Let `B` be a weakly admissible topological ring and let `f : B →+* A` be a flat ring map.
Then `f` is faithfully flat if and only if `B ⧸ J → A ⧸ JA` is faithfully flat for every weak
ideal of definition `J` of `B`, if and only if it is so for some weak ideal of definition. -/
public theorem faithfullyFlat_tfae_weakIdealOfDefinition {B : Type u} {A : Type v} [CommRing B]
    [CommRing A] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (hB : TopologicalRing.IsWeaklyAdmissible B) {f : B →+* A} (hf : f.Flat) :
    List.TFAE
      [ f.FaithfullyFlat,
        ∀ J : WeakIdealOfDefinitionIndex B, (quotientMapOfWeakIdeal f J).FaithfullyFlat,
        ∃ J : WeakIdealOfDefinitionIndex B, (quotientMapOfWeakIdeal f J).FaithfullyFlat ] := by
  tfae_have 1 → 2 := fun h J ↦ RingHom.faithfullyFlat_quotientMap f h J.1
  tfae_have 2 → 3 := fun h ↦ let ⟨J, hJ⟩ := hB.1; ⟨⟨J, hJ⟩, h _⟩
  tfae_have 3 → 1 := fun ⟨J, hJff⟩ ↦
    (RingHom.faithfullyFlat_iff_quotientMap f hf J.1
      (le_ringJacobson_of_isWeakIdealOfDefinition hB J.2)).mpr hJff
  tfae_finish

end TopologicalRing

end
