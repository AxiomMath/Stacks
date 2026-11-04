module

public import StacksFrontier.RingTheory.Flat.GeometricallyIrreducibleFibreLocus
public import StacksFrontier.RingTheory.GeometricallyIntegral.GoodReduced
public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromDenseFamily
public import StacksFrontier.RingTheory.GeometricallyReduced.SmoothLocus
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.RingTheory.Smooth.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The geometrically reduced fibre locus is constructible, and Stacks 05FT

`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedLocus` and
`StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut` reduce the affine case of Stacks 0579 —
constructibility of `Algebra.geometricallyReducedFibreLocus A C` for a Noetherian ring `A` and a
finite type `A`-algebra `C` — to the *good half* of the generic-fibre dichotomy, the affine case
of Stacks 0578 at the generic point: over a Noetherian domain `D` with a finite type algebra `T`
whose generic fibre is geometrically reduced, some nonempty basic open of `Spec D` lies inside
the locus. **This file proves that good half** from the smooth locus, and deduces Stacks 05FT from
the affine case of Stacks 0579, `Algebra.isConstructible_geometricallyReducedFibreLocus'`.

## The route

`StacksFrontier.RingTheory.GeometricallyIntegral.GoodReduced` shows that nothing can be gained by
working with constructible sets: granted the bad half, the good half and constructibility of the
locus are *equivalent*. The good half has to be proved by the argument of the source, which runs
through the smooth locus of `Spec T → Spec D`, and that is what happens here.

The smooth locus `U = Algebra.smoothLocus D T` is open, and `Spec T` is a Noetherian space, so
`U` is a finite union of standard opens `D(g₁), …, D(gₙ)` which it contains; each `T_{gⱼ}` is
therefore smooth over `D` (Stacks 00TB/00TC, in the form of Mathlib's
`Algebra.basicOpen_subset_smoothLocus_iff_smooth`), so all its fibres are geometrically reduced
(Stacks 033B, `Algebra.isReduced_of_smooth`, applied after base change). The family `1 ⊗ gⱼ` is
scheme-theoretically dense in the generic fibre: its union is the smooth locus of the generic
fibre by Stacks 00TG/02V4 (`Algebra.smoothLocus_comap_of_isPushout`), which contains every
minimal prime of the generic fibre because the generic fibre is geometrically reduced (Stacks
056V, in the affine form `Algebra.isSmoothAt_of_mem_minimalPrimes`), and an element of a reduced
ring annihilated by something outside every minimal prime is zero. Stacks 0573 and Stacks 056E
then spread that density to the nearby fibres, which is
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily'`.

## Main results

* `PrimeSpectrum.exists_fin_basicOpen_cover`: an open subset of the spectrum of a Noetherian ring
  is covered by finitely many standard opens each of which it contains.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_smoothLocus`:
  the good half, with the generic point given by an arbitrary flat field-valued point.
* `Algebra.projective_of_geometricallyIntegral_fibres`: **Stacks 05FT.** A flat algebra of finite
  presentation with geometrically integral fibres is projective as a module.
* `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_finiteType`: the geometrically
  integral fibre locus is constructible, which is Stacks 05DY combined with Stacks 055B and
  Stacks 0579.

## Implementation notes

The generic point is supplied as a field `K` over `D` with `D → K` injective and flat, rather
than as the fraction field, so that the hypothesis on the generic fibre can be stated as
`Algebra.IsGeometricallyReduced K (K ⊗[D] T)`; flatness is what Stacks 00TG asks of the base
change, and for the fraction field it is generic flatness in its simplest form. Every field `K`
over a domain `D` with `D → K` injective is in fact flat over `D`, since every nonzero element of
`D` becomes invertible in `K`, but that is not needed: the one `K` the argument uses is the
fraction field.

Neither Stacks 0578 nor Stacks 0579 is tagged here: what is proved here is the *affine* case of
each — the 0578 half below, the 0579 half as
`Algebra.isConstructible_geometricallyReducedFibreLocus'`, which this file consumes — while both
source statements are about an arbitrary morphism of schemes (`0578` about a morphism of finite
type to an irreducible base, `0579` about a quasi-compact morphism locally of finite
presentation). Both scheme-level statements are proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.OpenLocus`, which is where the two tags
sit, by a different route from this one: the locus is read on affine opens of the *target*, so
the passage runs through the Noetherian-free affine-base case rather than through the limit
argument of Stacks 01ZM. Stacks 05FT, by contrast, is a statement about a ring map and is proved
outright.

`Algebra.smoothLocus` is Mathlib's, defined by formal smoothness of the localizations; it agrees
with the Stacks definition 00TB for an algebra of finite presentation, and the only two facts
used about it are `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and
`Algebra.isOpen_smoothLocus`, both of which carry that hypothesis. It is available here because
`D` is Noetherian and `T` of finite type.

## References

* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 00TG](https://stacks.math.columbia.edu/tag/00TG)
* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 0573](https://stacks.math.columbia.edu/tag/0573)
* [Stacks Project, Tag 05DY](https://stacks.math.columbia.edu/tag/05DY)
-/

@[expose] public section

open PrimeSpectrum Topology

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace PrimeSpectrum

/-- **An open subset of the spectrum of a Noetherian ring is a finite union of standard opens.**
More precisely, there are finitely many `g₁, …, gₙ` with every `D(gⱼ)` inside the open set and
every point of the open set outside some `gⱼ`; so the open set is exactly `⋃ⱼ D(gⱼ)`.

A Noetherian ring has a Noetherian prime spectrum, in which every subset is quasi-compact, and
`PrimeSpectrum.isCompact_isOpen_iff` writes a quasi-compact open as the complement of the zero
locus of a finite set. -/
@[ega "I 1.1.10" "(i), Noetherian rings"]
public theorem exists_fin_basicOpen_cover {R : Type u} [CommRing R] [IsNoetherianRing R]
    {U : Set (PrimeSpectrum R)} (hU : IsOpen U) :
    ∃ (n : ℕ) (g : Fin n → R), (∀ j, (basicOpen (g j) : Set (PrimeSpectrum R)) ⊆ U) ∧
      ∀ p ∈ U, ∃ j, g j ∉ p.asIdeal := by
  obtain ⟨t, ht⟩ :=
    isCompact_isOpen_iff.mp ⟨TopologicalSpace.NoetherianSpace.isCompact U, hU⟩
  have hmem : ∀ x : R, x ∈ t → ∀ p : PrimeSpectrum R, x ∉ p.asIdeal → p ∈ U := by
    intro x hx p hxp
    rw [← ht]
    exact fun hp => hxp (hp hx)
  refine ⟨t.toList.length, fun j => t.toList.get j, fun j p hp => ?_, fun p hp => ?_⟩
  · exact hmem _ (Finset.mem_toList.mp (List.get_mem _ _)) p ((mem_basicOpen _ _).mp hp)
  · rw [← ht] at hp
    obtain ⟨x, hxt, hxp⟩ := Set.not_subset.mp fun hsub => hp (fun _ hy => hsub hy)
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hxt)
    exact ⟨j, by simp only [hj]; exact hxp⟩

end PrimeSpectrum

namespace Algebra

/-- **The good half of the generic-fibre dichotomy for reducedness, from the smooth locus.** Let
`D` be a Noetherian domain, `T` a finite type `D`-algebra and `K` a field over `D` which is flat
with `D → K` injective — the generic point of `Spec D`. If the generic fibre `K ⊗[D] T` is
geometrically reduced over `K`, then some nonempty basic open of `Spec D` is contained in
`Algebra.geometricallyReducedFibreLocus D T`.

This is the affine case of Stacks 0578 at the generic point. The smooth locus of `D → T` is open,
hence a finite union of standard opens `D(gⱼ)` with each `T_{gⱼ}` smooth over `D`; the fibres of
those are geometrically reduced by Stacks 033B, and the family `1 ⊗ gⱼ` is scheme-theoretically
dense in the generic fibre because by Stacks 00TG its union is the smooth locus of the generic
fibre, which by Stacks 056V contains every minimal prime of the geometrically reduced ring
`K ⊗[D] T`. The spreading out is then
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily'`. -/
public theorem
    exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_smoothLocus
    (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
    [Algebra.FiniteType D T] (K : Type u) [Field K] [Algebra D K] [Module.Flat D K]
    (hDK : Function.Injective (algebraMap D K))
    (hgeo : Algebra.IsGeometricallyReduced K (K ⊗[D] T)) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyReducedFibreLocus D T := by
  have : Algebra.FinitePresentation D T := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing D T
  obtain ⟨n, g, hgsub, hgcov⟩ :=
    PrimeSpectrum.exists_fin_basicOpen_cover
      (U := Algebra.smoothLocus D T) Algebra.isOpen_smoothLocus
  refine exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily' g K hDK
    ?_ ?_
  · rw [bigPhi_injective_iff_commonAnnihilator]
    intro m hm
    refine Algebra.eq_zero_of_forall_exists_notMem_smoothLocus (k := K) fun p hp => ?_
    rw [← Algebra.smoothLocus_comap_of_isPushout D T K (K ⊗[D] T)] at hp
    obtain ⟨j, hj⟩ := hgcov _ hp
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hj
    refine ⟨(1 : K) ⊗ₜ[D] g j, ?_, by simpa [smul_eq_mul] using hm j⟩
    exact fun hmem => hj hmem
  · intro L _ _ j
    have : Algebra.Smooth D (Localization.Away (g j)) :=
      Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp (hgsub j)
    exact Algebra.isReduced_of_smooth L (L ⊗[D] Localization.Away (g j))

/-- **Stacks Project, Tag 05FT.** Let `R → S` be flat and of finite presentation and suppose that
every fibre ring `S ⊗[R] κ(p)` is geometrically integral over `κ(p)`. Then `S` is a projective
`R`-module.

This is `Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible_reduced` with its
hypothesis — constructibility of the geometrically reduced fibre locus over a Noetherian base,
the affine case of Stacks 0579 — discharged by
`Algebra.isConstructible_geometricallyReducedFibreLocus'`. The irreducible half was
discharged by `Algebra.isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType`, the
affine case of the level set `n = 1` of Stacks 055B. -/
@[stacks 05FT]
public theorem projective_of_geometricallyIntegral_fibres {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField)) :
    Module.Projective R S :=
  projective_of_geometricallyIntegral_fibres_of_isConstructible_reduced
    (fun A C _ _ _ _ _ => isConstructible_geometricallyReducedFibreLocus' A C) h

/-- **The geometrically integral fibre locus is constructible.** For a Noetherian ring `A` and a
finite type `A`-algebra `C`, the set of primes of `A` whose fibre is geometrically integral is
constructible in `Spec A`.

Stacks 05DY splits the condition into geometric irreducibility and geometric reducedness, and the
two halves are now available unconditionally:
`Algebra.isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType` and
`Algebra.isConstructible_geometricallyReducedFibreLocus'`. -/
public theorem isConstructible_geometricallyIntegralFibreLocus_of_finiteType
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIntegralFibreLocus A C) :=
  isConstructible_geometricallyIntegralFibreLocus A C
    (isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType A C)
    (isConstructible_geometricallyReducedFibreLocus' A C)

end Algebra

end
