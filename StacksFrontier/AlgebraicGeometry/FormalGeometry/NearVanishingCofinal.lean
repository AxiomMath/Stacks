module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.NearVanishing

/-!
# Complements of zero loci are cofinal among the neighbourhoods of the formal locus

Let `I` and `𝔞` be ideals of a commutative ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `J₀` be an
ideal with `V(J₀) ∩ V(I) = V(𝔞)`. Every neighbourhood `V ⊆ U` of the formal locus `U ∩ V(I)`
(`Stacks.Algebraization.OpensNearVanishing`) contains one of the form `U ∩ (Spec(A) ∖ V(J))` for
an ideal `J ⊆ J₀` with again `V(J) ∩ V(I) = V(𝔞)`. So a colimit over the neighbourhoods of the
formal locus, such as the sections of a module near the formal locus, is computed on these
complements alone, whose cohomology is local cohomology supported in `V(J)`.

## Main definitions

* `Stacks.Algebraization.OpensNearVanishing.ofIdeal`: the neighbourhood `U ∩ (Spec(A) ∖ V(J))`
  of the formal locus, for an ideal `J` with `V(J) ∩ V(I) ⊆ V(𝔞)`.

## Main results

* `Stacks.Algebraization.OpensNearVanishing.exists_ofIdeal_le`: every neighbourhood of the
  formal locus contains `U ∩ (Spec(A) ∖ V(J))` for some `J ⊆ J₀` with `V(J) ∩ V(I) = V(𝔞)`.

## References

* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- **The neighbourhood `U ∩ (Spec(A) ∖ V(J))` of the formal locus**, for an ideal `J` whose zero
locus meets `V(I)` only inside `V(𝔞)`: a point of `U` lying over `V(I)` is then outside `V(J)`. -/
def OpensNearVanishing.ofIdeal (A : Type u) [CommRing A] (I a J : Ideal A)
    (hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
      PrimeSpectrum.zeroLocus (a : Set A)) :
    OpensNearVanishing A I a where
  openSet := (complementZeroLocus A a).ι ⁻¹ᵁ complementZeroLocus A J
  contains_vanishing x hx hxJ :=
    x.2 (hJ ⟨hxJ, (PrimeSpectrum.mem_zeroLocus _ _).2 hx⟩)

/-- The open set of `OpensNearVanishing.ofIdeal A I a J hJ` is the preimage in `U` of
`Spec(A) ∖ V(J)`. -/
@[simp]
theorem OpensNearVanishing.ofIdeal_openSet (A : Type u) [CommRing A] (I a J : Ideal A)
    (hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
      PrimeSpectrum.zeroLocus (a : Set A)) :
    (OpensNearVanishing.ofIdeal A I a J hJ).openSet =
      (complementZeroLocus A a).ι ⁻¹ᵁ complementZeroLocus A J :=
  rfl

/-- **Every neighbourhood of the formal locus contains `U ∩ (Spec(A) ∖ V(J))` for an ideal
`J ⊆ J₀` with `V(J) ∩ V(I) = V(𝔞)`**, provided `V(J₀) ∩ V(I) = V(𝔞)` (which forces
`V(𝔞) ⊆ V(I)`; no inclusion `I ⊆ 𝔞` is needed). -/
theorem OpensNearVanishing.exists_ofIdeal_le {A : Type u} [CommRing A] {I a : Ideal A}
    {J₀ : Ideal A}
    (hJ₀ : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A))
    (V : OpensNearVanishing A I a) :
    ∃ (J : Ideal A) (_ : J ≤ J₀)
      (hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A)),
      Nonempty (V ⟶ OpensNearVanishing.ofIdeal A I a J hJ.le) := by
  let W : (Spec (CommRingCat.of A)).Opens := (complementZeroLocus A a).ι ''ᵁ V.openSet
  let C : Set (PrimeSpectrum A) := fun p => p ∉ (W : Set (Spec (CommRingCat.of A)))
  let K : Ideal A := PrimeSpectrum.vanishingIdeal C
  have hK : PrimeSpectrum.zeroLocus (K : Set A) = C := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact W.isOpen.isClosed_compl.closure_eq
  have hmemC : ∀ x : (complementZeroLocus A a : Scheme), x.1 ∈ C ↔ x ∉ V.openSet := by
    intro x
    refine not_congr ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨x, hx, rfl⟩⟩
    exact (Subtype.ext hyx : y = x) ▸ hy
  let J : Ideal A := K ⊓ J₀
  have hJzero : PrimeSpectrum.zeroLocus (J : Set A) =
      PrimeSpectrum.zeroLocus (K : Set A) ∪ PrimeSpectrum.zeroLocus (J₀ : Set A) :=
    PrimeSpectrum.zeroLocus_inf K J₀
  have hKI : PrimeSpectrum.zeroLocus (K : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
      PrimeSpectrum.zeroLocus (a : Set A) := by
    rintro p ⟨hpK, hpI⟩
    by_contra hpa
    let x : (complementZeroLocus A a : Scheme) := ⟨p, hpa⟩
    exact (hmemC x).1 (hK ▸ hpK : x.1 ∈ C)
      (V.contains_vanishing x ((PrimeSpectrum.mem_zeroLocus _ _).1 hpI))
  have hJI : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) := by
    rw [hJzero, Set.union_inter_distrib_right, hJ₀]
    exact Set.union_eq_right.2 hKI
  refine ⟨J, inf_le_right, hJI, ⟨⟨?_⟩⟩⟩
  intro x hx
  by_contra hxV
  have hxK : x.1 ∈ PrimeSpectrum.zeroLocus (K : Set A) := hK ▸ (hmemC x).2 hxV
  exact hx (hJzero ▸ Or.inl hxK)

end Stacks.Algebraization

end
