module

public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedLocus

/-!
# The geometrically irreducible fibre locus, and Stacks 05FT from one generic-fibre statement

Stacks 055B says that for a morphism of finite presentation the level sets of the function counting
the geometrically irreducible components of the fibres are locally constructible. Only the level
set `n = 1` is needed for Stacks 05FT, and only over an affine Noetherian base: the statement that
`Algebra.geometricallyIrreducibleFibreLocus A C` is constructible in `Spec A`.

Both Stacks 055B and Stacks 0579 are proved from the constructibility criterion of Stacks 053Z
together with a statement about the generic fibre over an integral base — here Stacks 055A, that
the number of geometrically irreducible components of the fibres is constant on a nonempty open of
any irreducible closed subset of the base. The criterion and the reduction to an integral base are
carried out, once for any iso-invariant property of the fibres, in
`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedLocus`; this file instantiates that
machinery at irreducibility of the spectrum, and then at being a domain, which is what Stacks
05FT needs.

The upshot is `Algebra.projective_of_geometricallyIntegral_fibres_of_spreadOut`: Stacks 05FT holds
granted the single statement that over a Noetherian domain some nonempty basic open of the base
either lies in or misses the geometrically integral fibre locus. That statement is about the fibres
near the generic point of an integral base — it is EGA IV 9.7.7 read at the generic point, and the
conjunction of the affine cases of Stacks 0577, 0578 and 055A, as
`Algebra.exists_basicOpen_geometricallyIntegral` records. Neither Noetherian approximation nor any
topology on the base is left.

## Main results

* `Algebra.isConstructible_geometricallyIrreducibleFibreLocus`: the affine case of the level set
  `n = 1` of Stacks 055B, conditional on the affine case of Stacks 055A.
* `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_spreadOut`: the remaining hypothesis
  of `Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible` reduced to the
  generic-fibre dichotomy for geometric integrality.
* `Algebra.exists_basicOpen_geometricallyIntegral`: that dichotomy follows from the two halves of
  Stacks 05DY, the dichotomy for geometric reducedness and the one for geometric irreducibility.
* `Algebra.projective_of_geometricallyIntegral_fibres_of_spreadOut`: Stacks 05FT itself, granted
  the dichotomy for geometric integrality.

## Implementation notes

The fibre property used in `Algebra.geometricallyIrreducibleFibreLocus` is
`IrreducibleSpace (PrimeSpectrum R)`, and in `Algebra.geometricallyIntegralFibreLocus` it is
`IsDomain R`; the first is invariant under ring isomorphism because a ring isomorphism induces a
homeomorphism of spectra (`PrimeSpectrum.homeomorphOfRingEquiv`), the second because an isomorphism
is injective.

Nothing here carries a `@[stacks 055B]` or `@[stacks 05FT]` attribute: all the statements are
conditional on a generic-fibre dichotomy, and a conditional statement tagged with the tag of an
unconditional one would misreport what is proved. Both dichotomies have since been supplied —
the irreducible one in
`StacksFrontier.RingTheory.Flat.GeometricallyIrreducibleFibreLocus` and the reduced one in
`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromSmoothLocus` — so Stacks 05FT is
proved there, as `Algebra.projective_of_geometricallyIntegral_fibres`; Stacks 055B remains
untagged because only the affine case of its level set `n = 1` is available in this form.

## References

* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
* [Stacks Project, Tag 0555](https://stacks.math.columbia.edu/tag/0555)
* [Stacks Project, Tag 053Z](https://stacks.math.columbia.edu/tag/053Z)
* [Stacks Project, Tag 05DY](https://stacks.math.columbia.edu/tag/05DY)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat Topology
open scoped TensorProduct

universe u

namespace Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The geometrically irreducible fibre locus is the fibre locus of the property that the spectrum
is irreducible. -/
theorem geometricallyIrreducibleFibreLocus_eq_fibreLocus (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] :
    geometricallyIrreducibleFibreLocus A C =
      fibreLocus A C (fun R _ => IrreducibleSpace (PrimeSpectrum R)) := rfl

/-- The geometrically integral fibre locus is the fibre locus of the property of being a domain. -/
theorem geometricallyIntegralFibreLocus_eq_fibreLocus (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] :
    geometricallyIntegralFibreLocus A C = fibreLocus A C (fun R _ => IsDomain R) := rfl

/-- Irreducibility of the spectrum is invariant under ring isomorphism, a ring isomorphism
inducing a homeomorphism of spectra. -/
theorem irreducibleSpace_primeSpectrum_congr {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IrreducibleSpace (PrimeSpectrum R) ↔ IrreducibleSpace (PrimeSpectrum S) :=
  (PrimeSpectrum.homeomorphOfRingEquiv e).irreducibleSpace_iff

/-- Being a domain is invariant under ring isomorphism. -/
theorem isDomain_congr {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    IsDomain R ↔ IsDomain S :=
  ⟨fun _ => e.symm.injective.isDomain, fun _ => e.injective.isDomain⟩

/-- **The affine case of the level set `n = 1` of Stacks 055B, granted the affine case of Stacks
055A.** Let `A` be a Noetherian ring and `C` a finite type `A`-algebra. If over every Noetherian
domain `D` and finite type `D`-algebra `T` some nonempty basic open of `Spec D` either lies in or
misses the geometrically irreducible fibre locus of `T`, then the geometrically irreducible fibre
locus of `C` is constructible in `Spec A`.

The hypothesis is the dichotomy supplied by Stacks 055A: the number of geometrically irreducible
components of the fibres is constant on a nonempty open around the generic point, so either every
fibre there is geometrically irreducible or none is. -/
theorem isConstructible_geometricallyIrreducibleFibreLocus
    (hspread : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T], ∃ f : D, f ≠ 0 ∧
        ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
            geometricallyIrreducibleFibreLocus D T ∨
          Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D))
            (geometricallyIrreducibleFibreLocus D T)))
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIrreducibleFibreLocus A C) := by
  rw [geometricallyIrreducibleFibreLocus_eq_fibreLocus]
  exact isConstructible_fibreLocus (fun _ _ _ _ e => irreducibleSpace_primeSpectrum_congr e)
    hspread A C

/-- **The remaining hypothesis of Stacks 05FT, reduced to one generic-fibre dichotomy.** Let `A` be
a Noetherian ring and `C` a finite type `A`-algebra. If over every Noetherian domain `D` and finite
type `D`-algebra `T` some nonempty basic open of `Spec D` either lies in or misses the
geometrically integral fibre locus of `T`, then the geometrically integral fibre locus of `C` is
constructible in `Spec A`.

This is the affine case of Stacks 0579 and Stacks 055B combined, in the form the proof of Stacks
05FT consumes them; the hypothesis is the affine case of EGA IV 9.7.7 at the generic point of an
integral base. -/
theorem isConstructible_geometricallyIntegralFibreLocus_of_spreadOut
    (hspread : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T], ∃ f : D, f ≠ 0 ∧
        ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
            geometricallyIntegralFibreLocus D T ∨
          Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D))
            (geometricallyIntegralFibreLocus D T)))
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIntegralFibreLocus A C) := by
  rw [geometricallyIntegralFibreLocus_eq_fibreLocus]
  exact isConstructible_fibreLocus (fun _ _ _ _ e => isDomain_congr e) hspread A C

/-- **The generic-fibre dichotomy for geometric integrality from its two halves.** Over a domain
`D`, if some nonempty basic open either lies in or misses the geometrically reduced fibre locus of
`T`, and likewise for the geometrically irreducible fibre locus, then some nonempty basic open
either lies in or misses the geometrically integral fibre locus.

By Stacks 05DY the integral locus is the intersection of the other two. If both alternatives are
inclusions, the product of the two elements works, a basic open of a product being the intersection
of the basic opens; if either alternative is a disjointness, that element already works, the
integral locus being contained in each half. -/
theorem exists_basicOpen_geometricallyIntegral (D T : Type u) [CommRing D] [IsDomain D]
    [CommRing T] [Algebra D T]
    (hred : ∃ f : D, f ≠ 0 ∧
      ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆ geometricallyReducedFibreLocus D T ∨
        Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D))
          (geometricallyReducedFibreLocus D T)))
    (hirr : ∃ g : D, g ≠ 0 ∧
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T ∨
        Disjoint (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum D))
          (geometricallyIrreducibleFibreLocus D T))) :
    ∃ h : D, h ≠ 0 ∧
      ((PrimeSpectrum.basicOpen h : Set (PrimeSpectrum D)) ⊆
          geometricallyIntegralFibreLocus D T ∨
        Disjoint (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum D))
          (geometricallyIntegralFibreLocus D T)) := by
  obtain ⟨f, hf0, hfcase⟩ := hred
  obtain ⟨g, hg0, hgcase⟩ := hirr
  have hinter := geometricallyIntegralFibreLocus_eq_inter D T
  rcases hfcase with hfsub | hfdisj
  · rcases hgcase with hgsub | hgdisj
    · refine ⟨f * g, mul_ne_zero hf0 hg0, Or.inl fun x hx => ?_⟩
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hx
      rw [hinter]
      exact ⟨hgsub (PrimeSpectrum.mem_basicOpen g x |>.mpr
          fun hg => hx (x.asIdeal.mul_mem_left f hg)),
        hfsub (PrimeSpectrum.mem_basicOpen f x |>.mpr
          fun hgf => hx (x.asIdeal.mul_mem_right g hgf))⟩
    · exact ⟨g, hg0, Or.inr (hinter ▸ hgdisj.mono_right Set.inter_subset_left)⟩
  · exact ⟨f, hf0, Or.inr (hinter ▸ hfdisj.mono_right Set.inter_subset_right)⟩

/-- **Stacks 05FT from one generic-fibre dichotomy.** Let `R → S` be flat of finite presentation
and suppose `S ⊗[R] κ(p)` is geometrically integral over `κ(p)` for every prime `p` of `R`. Then
`S` is a projective `R`-module, provided that over every Noetherian domain `D` and every finite
type `D`-algebra `T` some nonempty basic open of `Spec D` either lies in or misses the
geometrically integral fibre locus of `T`.

This is `Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible` with its single
hypothesis discharged by
`Algebra.isConstructible_geometricallyIntegralFibreLocus_of_spreadOut`. What remains is the affine
case of EGA IV 9.7.7 at the generic point of an integral base; by
`Algebra.exists_basicOpen_geometricallyIntegral` it suffices to prove the two halves separately,
which are the affine cases of Stacks 0577 together with Stacks 0578, and of Stacks 055A. -/
theorem projective_of_geometricallyIntegral_fibres_of_spreadOut
    (hspread : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T], ∃ f : D, f ≠ 0 ∧
        ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
            geometricallyIntegralFibreLocus D T ∨
          Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D))
            (geometricallyIntegralFibreLocus D T)))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField)) :
    Module.Projective R S :=
  projective_of_geometricallyIntegral_fibres_of_isConstructible
    (fun R₀ S₀ _ _ _ _ _ _ =>
      isConstructible_geometricallyIntegralFibreLocus_of_spreadOut hspread R₀ S₀) h

end Algebra

end
