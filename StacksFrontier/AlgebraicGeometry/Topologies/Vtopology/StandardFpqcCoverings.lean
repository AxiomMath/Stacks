module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Scheme.Valuative.Specialization
public import StacksFrontier.AlgebraicGeometry.Topologies.V.StandardCoverings

/-!
# Standard fpqc coverings are standard V coverings

A finite jointly surjective family of flat morphisms from affine schemes to an affine scheme
satisfies the valuation-ring lifting property of a standard V covering.

## Main results

* `AlgebraicGeometry.isStandardVCovering_of_flat_affineCover` says that a finite affine cover by
  flat morphisms is a standard V covering.

## Implementation notes

Mathlib's `Scheme.AffineCover` packages the affine sources and joint surjectivity of the family.
Taking its morphism property to be `Flat` and requiring its index type to be finite is precisely
a standard fpqc covering.

## References

* [Stacks Project, Tag 0ETC](https://stacks.math.columbia.edu/tag/0ETC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- A standard fpqc covering of an affine scheme is a standard V covering. -/
@[stacks 0ETC]
theorem isStandardVCovering_of_flat_affineCover
    {T : Scheme.{u}} [IsAffine T] (𝒰 : T.AffineCover.{v} @Flat) [Finite 𝒰.I₀] :
    AlgebraicGeometry.IsStandardVCovering (fun i ↦ Spec (𝒰.X i)) 𝒰.f := by
  intro V _ _ _ g
  let i := 𝒰.idx (g (IsLocalRing.closedPoint V))
  obtain ⟨xi, hxi⟩ := 𝒰.covers (g (IsLocalRing.closedPoint V))
  obtain ⟨z, hzfst, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := g) (g := 𝒰.f i)
      (IsLocalRing.closedPoint V) xi hxi.symm
  have : Flat (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨z', hz'spec, hz'fst⟩ :=
    (Flat.generalizingMap (pullback.fst g (𝒰.f i)))
      (by rw [hzfst]; exact genericPoint_specializes (IsLocalRing.closedPoint V))
  let K : Type u := (pullback g (𝒰.f i)).residueField z'
  obtain ⟨W, _, _, _, h, eK, hgeneric, hclosed, -⟩ :=
    AlgebraicGeometry.exists_valuation_ring_of_specializes (pullback g (𝒰.f i)) hz'spec K
      (CategoryTheory.Iso.refl _).hom
  let e : V →+* W := (Spec.preimage (h ≫ pullback.fst g (𝒰.f i))).hom
  have he : Spec.map (CommRingCat.ofHom e) = h ≫ pullback.fst g (𝒰.f i) := by simp [e]
  have hpt (x) : Spec.map (CommRingCat.ofHom e) x = pullback.fst g (𝒰.f i) (h x) := by
    rw [he]; rfl
  refine ⟨W, inferInstance, inferInstance, inferInstance, e, ?_, i,
    h ≫ pullback.snd g (𝒰.f i), ?_⟩
  · constructor
    · rw [RingHom.injective_iff_ker_eq_bot]
      change Ideal.comap e ⊥ = ⊥
      have hegeneric : Spec.map (CommRingCat.ofHom e) (genericPoint (Spec (.of W))) =
          genericPoint (Spec (.of V)) := (hpt _).trans (by rw [hgeneric, hz'fst]; rfl)
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine] at hegeneric
      change PrimeSpectrum.comap e (⊥ : PrimeSpectrum W) = (⊥ : PrimeSpectrum V) at hegeneric
      simpa only [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot] using
        congrArg PrimeSpectrum.asIdeal hegeneric
    · rw [IsLocalRing.isLocalHom_iff_comap_closedPoint]
      exact (hpt _).trans (by rw [hclosed, hzfst])
  · simp only [he, Category.assoc, pullback.condition]

end AlgebraicGeometry
