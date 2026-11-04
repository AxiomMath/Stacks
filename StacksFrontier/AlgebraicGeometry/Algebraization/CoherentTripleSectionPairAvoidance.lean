module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPair
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleInvertible
public import StacksFrontier.RingTheory.Ideal.FinitePrimeAvoidance

/-!
# Prime avoidance on the punctured spectrum

Let `A` be a local ring with maximal ideal `𝔪`. A finite set of points of the punctured spectrum
of `A` lies in the basic open of some `g ∈ 𝔪`. For a fixed invertible triple `L` and a triple `T`,
this gives a global section `x` of `L.F` and a `g ∈ 𝔪` such that every section `g^N x` is
nonvanishing at the associated points of `T.F` and of `T.F / f T.F`.

## Main results

* `Stacks.Algebraization.basicOpen_puncturedScalars`: the basic open on the punctured spectrum of
  the image of a ring element is the preimage of its basic open in `Spec A`.
* `Stacks.Algebraization.mem_basicOpen_puncturedScalars`: a point of the punctured spectrum lies
  in the basic open of the image of `g` exactly when `g` is outside the corresponding prime.
* `Stacks.Algebraization.exists_mem_maximalIdeal_subset_basicOpen`: prime avoidance on the
  punctured spectrum: any finite set of points lies in the basic open of some `g ∈ 𝔪`.
* `Stacks.Algebraization.exists_mem_maximalIdeal_nonvanishing_smul_pow`: a global section `x` of
  `L.F` and a `g ∈ 𝔪` such that every `g^N x` is nonvanishing on `Ass(T.F) ∪ Ass(T.F / f T.F)`.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.AlgebraicGeometry.PrincipalIdealExtension

universe u

namespace Stacks.Algebraization

/-! ### Basic opens on the punctured spectrum -/

/-- The basic open on the punctured spectrum of the image of a ring element `g` is the preimage
of the basic open of `g` in `Spec A`. -/
public theorem basicOpen_puncturedScalars (A : Type u) [CommRing A] [IsLocalRing A] (g : A) :
    (Stacks.Divisors.puncturedSpectrum A).toScheme.basicOpen (puncturedScalars A g) =
      (Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ
        (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) :=
  (Scheme.preimage_basicOpen_top (Stacks.Divisors.puncturedSpectrum A).ι _).symm

/-- A point of the punctured spectrum lies in the basic open of the image of `g` exactly when `g`
is outside the corresponding prime. -/
public theorem mem_basicOpen_puncturedScalars (A : Type u) [CommRing A] [IsLocalRing A] (g : A)
    (x : (Stacks.Divisors.puncturedSpectrum A).toScheme) :
    x ∈ (Stacks.Divisors.puncturedSpectrum A).toScheme.basicOpen (puncturedScalars A g) ↔
      g ∉ x.1.asIdeal := by
  simp only [basicOpen_puncturedScalars, basicOpen_eq_of_affine (R := CommRingCat.of A) g]
  exact PrimeSpectrum.mem_basicOpen g x.1

/-! ### Prime avoidance on the punctured spectrum -/

/-- **Prime avoidance on the punctured spectrum.** A finite set of points of the punctured
spectrum of a local ring lies in the basic open of some element of the maximal ideal. -/
public theorem exists_mem_maximalIdeal_subset_basicOpen (A : Type u) [CommRing A] [IsLocalRing A]
    {E : Set (Stacks.Divisors.puncturedSpectrum A).toScheme} (hE : E.Finite) :
    ∃ g ∈ maximalIdeal A,
      E ⊆ ((Stacks.Divisors.puncturedSpectrum A).toScheme.basicOpen
        (puncturedScalars A g) : Set _) := by
  obtain ⟨g, hgm, hg⟩ := exists_mem_forall_notMem_of_forall_not_le
    (I := maximalIdeal A)
    (hE.image fun x : (Stacks.Divisors.puncturedSpectrum A).toScheme => x.1.asIdeal)
    (by rintro _ ⟨x, -, rfl⟩; exact x.1.isPrime)
    (by
      rintro _ ⟨x, -, rfl⟩ hle
      exact x.2 (PrimeSpectrum.ext (le_antisymm (le_maximalIdeal x.1.isPrime.ne_top) hle)))
  exact ⟨g, hgm, fun x hx => (mem_basicOpen_puncturedScalars A g x).2
    (hg _ ⟨x, hx, rfl⟩)⟩

/-! ### A nonvanishing section that survives multiplication -/

/-- For an invertible triple `L` and any triple `T` over a Noetherian local ring there are a
global section `x` of `L.F` and a `g ∈ 𝔪` such that for every exponent `N` the section `g^N x`
does not vanish at any point of `Ass(T.F) ∪ Ass(T.F / f T.F)`. -/
public theorem exists_mem_maximalIdeal_nonvanishing_smul_pow {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (T : CoherentTriple A f) :
    letI := hL.invertible_F
    ∃ (g : A) (_ : g ∈ maximalIdeal A) (x : Γ(L.F, ⊤)), ∀ N : ℕ,
      (Stacks.Divisors.associatedPoints T.F ∪
          Stacks.Divisors.associatedPoints
            (cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1))) ⊆
        (Stacks.NonvanishingOpen.nonvanishingOpen
          (Stacks.Divisors.puncturedSpectrum A).toScheme L.F
          (puncturedScalars A g ^ N • x) : Set _) := by
  let := hL.invertible_F
  have := T.coherent_F
  obtain ⟨x, hx⟩ := exists_section_nonvanishing_on_associatedPoints hL T
  obtain ⟨g, hgm, hg⟩ := exists_mem_maximalIdeal_subset_basicOpen A
    (Stacks.Divisors.associatedPoints_union_cokernel_smulPowHom_finite_puncturedSpectrum A T.F
      (scalarOnOpen A f ⊤) 1)
  refine ⟨g, hgm, x, fun N => ?_⟩
  rcases N with _ | n
  · simpa using hx
  refine fun y hy => ?_
  have hbo : y ∈ ((Stacks.Divisors.puncturedSpectrum A).toScheme.basicOpen
      (puncturedScalars A g ^ (n + 1)) : Set _) := by
    rw [Scheme.basicOpen_pow (X := (Stacks.Divisors.puncturedSpectrum A).toScheme)
      (f := puncturedScalars A g) n.succ_pos]
    exact hg hy
  simp only [Stacks.NonvanishingOpen.coe_nonvanishingOpen] at hx ⊢
  rw [Stacks.Ample.nonvanishingLocus_smul]
  exact ⟨hbo, hx hy⟩

end Stacks.Algebraization

end
