module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.RingTheory.PseudoCoherentMap.FiniteFreeDescent

/-!
# Descent of pseudo-coherence along a surjective finite locally free morphism

Let `h : T ⟶ W` be a surjective finite locally free morphism and `f : W ⟶ Y` a morphism of
schemes. If the composition `h ≫ f` is pseudo-coherent, then so is `f`.

This is the finite locally free step in the proof that pseudo-coherence of a morphism of schemes
is fppf local on the source: an fppf covering is refined by Zariski open covers together with
surjective finite locally free morphisms, so this statement and the Zariski locality of
pseudo-coherence are what that locality reduces to.

Over an affine base the direct image of the structure sheaf of a finite locally free morphism is
only *locally* free, so the affine case cannot be applied to an arbitrary affine open of `W`.
What makes the reduction work is that pseudo-coherence may be tested on one pair of opens around
each point of the source: around a point `w` of `W` one first picks an affine open `U` of `Y`
containing `f w`, and only then shrinks `W` to an affine open `V` that lies inside `f ⁻¹ᵁ U` and
is small enough to trivialise the direct image. Over such a `V` the sections of the structure
sheaf of `T` really are finite free, and the affine case applies.

## Main results

* `AlgebraicGeometry.pseudoCoherent_of_comp_surjective_finiteLocallyFree_of_isAffine`: the
  descent for a surjective finite locally free morphism of affine schemes whose direct image of
  the structure sheaf is free.
* `AlgebraicGeometry.pseudoCoherent_of_comp_surjective_finiteLocallyFree`: the descent for an
  arbitrary surjective finite locally free morphism.

## Implementation notes

Zariski locality of pseudo-coherence at the target is the instance
`AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtTarget`. Zariski locality at the source and
stability under composition with an open immersion are supplied by `have` rather than by instance
synthesis. Mathlib's `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource` does not
apply to `@AlgebraicGeometry.PseudoCoherent` in type class search, for the reason given at
`AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtTarget`, and the instance
`AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtSource` lives in a module this one does not
import. Stability under composition with an open immersion is
`AlgebraicGeometry.HasRingHomProperty.respects_isOpenImmersion`, a lemma with a hypothesis on
`RingHom.PseudoCoherent` rather than an instance.

The affine case is stated with the freeness of the sections as a hypothesis rather than derived
from finite local freeness, because finite local freeness of a morphism onto an affine scheme
does not imply that the sections are free.

## References

* [The Stacks Project, Lemma 37.60.14 (0699)](https://stacks.math.columbia.edu/tag/0699)
* [The Stacks Project, Lemma 37.60.13 (0698)](https://stacks.math.columbia.edu/tag/0698)
* [The Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [The Stacks Project, Definition 15.83.1 (067H)](https://stacks.math.columbia.edu/tag/067H)
-/

@[expose] public section

open CategoryTheory Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-- **Descent of pseudo-coherence along a surjective finite locally free morphism of affine
schemes with free sections.** Let `h : T ⟶ W` be a surjective finite locally free morphism of
affine schemes whose global sections are free over those of `W`, and let `f : W ⟶ Y` be a
morphism to an affine scheme. If `h ≫ f` is pseudo-coherent, then so is `f`.

On global sections `h` is a finite free faithfully flat ring map: finiteness comes from
finiteness of `h`, freeness is the hypothesis, and faithful flatness is flatness of `h` together
with its surjectivity. So this is `Algebra.PseudoCoherent.of_finite_free_faithfullyFlat`. -/
theorem pseudoCoherent_of_comp_surjective_finiteLocallyFree_of_isAffine
    {T W Y : Scheme.{u}} [IsAffine T] [IsAffine W] [IsAffine Y]
    (h : T ⟶ W) (f : W ⟶ Y) (hsurj : Surjective h) (hh : IsFiniteLocallyFree h)
    (hfree : letI := h.appTop.hom.toAlgebra; Module.Free Γ(W, ⊤) Γ(T, ⊤))
    (hcomp : PseudoCoherent (h ≫ f)) : PseudoCoherent f := by
  have : IsFiniteLocallyFree h := hh
  rw [HasRingHomProperty.iff_of_isAffine (P := @PseudoCoherent)]
  algebraize [f.appTop.hom, h.appTop.hom, h.appTop.hom.comp f.appTop.hom]
  have : Module.Free Γ(W, ⊤) Γ(T, ⊤) := hfree
  have : Module.FaithfullyFlat Γ(W, ⊤) Γ(T, ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine h).mp
        ⟨IsFiniteLocallyFree.flat h, hsurj⟩)
  have : Module.Finite Γ(W, ⊤) Γ(T, ⊤) := by
    have := IsFiniteLocallyFree.isFinite h
    exact RingHom.finite_algebraMap.mp h.finite_appTop
  have hcomp' : RingHom.PseudoCoherent (h.appTop.hom.comp f.appTop.hom) := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      HasRingHomProperty.appTop (P := @PseudoCoherent) (h ≫ f) hcomp
  exact hcomp'.of_finite_free_faithfullyFlat

/-- **Descent of pseudo-coherence along a surjective finite locally free morphism.** Let
`h : T ⟶ W` be surjective and finite locally free and let `f : W ⟶ Y` be a morphism of schemes.
If `h ≫ f` is pseudo-coherent, then so is `f`.

Pseudo-coherence is Zariski local at the source and at the target and is stable under
composition with an open immersion, so it suffices to produce, for each point `w` of `W`, opens
`U` of `Y` and `V` of `W` with `w ∈ V` and `V ⊆ f ⁻¹ᵁ U` for which the induced morphism
`V ⟶ U` is pseudo-coherent. Choosing `U` affine around `f w` first, and then `V` affine inside
the intersection of `f ⁻¹ᵁ U` with an open that trivialises the direct image of the structure
sheaf of `T`, makes the sections of `T` over `h ⁻¹ᵁ V` finite free over those of `W` over `V`,
and the restriction of `h` over `V` is still surjective and finite locally free. The affine case
then applies, with `h ≫ f` restricted over `U` and `h ⁻¹ᵁ V` supplying the hypothesis. -/
theorem pseudoCoherent_of_comp_surjective_finiteLocallyFree
    {T W Y : Scheme.{u}} (h : T ⟶ W) (f : W ⟶ Y) (hsurj : Surjective h)
    (hh : IsFiniteLocallyFree h) (hcomp : PseudoCoherent (h ≫ f)) : PseudoCoherent f := by
  have hflf : IsFiniteLocallyFree h := hh
  have hsu : Surjective h := hsurj
  have hls : IsZariskiLocalAtSource (@PseudoCoherent.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.PseudoCoherent)
  have hroi : MorphismProperty.Respects
      (@PseudoCoherent.{u} : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    HasRingHomProperty.respects_isOpenImmersion (P := @PseudoCoherent.{u})
      (Q := @RingHom.PseudoCoherent)
      RingHom.pseudoCoherent_stableUnderCompositionWithLocalizationAway.1
  have : MorphismProperty.RespectsRight
      (@PseudoCoherent.{u} : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    hroi.toRespectsRight
  rw [IsZariskiLocalAtSource.iff_exists_resLE (P := @PseudoCoherent.{u})]
  intro w
  -- An affine open of the target around the image of `w`.
  obtain ⟨U, hU, hfw, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f.base w ∈ (⊤ : Y.Opens) from trivial)
  -- An open around `w` trivialising the direct image of the structure sheaf of `T`.
  obtain ⟨O, hwO, I, -, ⟨e⟩⟩ := ((isFiniteLocallyFree_iff_pointwise h).mp hflf).2 w
  -- An affine open inside both.
  obtain ⟨V, hV, hwV, hVle⟩ := exists_isAffineOpen_mem_and_subset
    (show w ∈ O ⊓ (f ⁻¹ᵁ U) from ⟨hwO, hfw⟩)
  have hle : V ≤ f ⁻¹ᵁ U := fun x hx => (hVle hx).2
  refine ⟨U, V, hwV, hle, ?_⟩
  -- The trivialisation restricts to `V`, so the sections of `T` over `h ⁻¹ᵁ V` are free.
  have hr : Set.range V.ι.base ⊆ Set.range O.ι.base := by
    simpa [Scheme.Opens.range_ι] using hVle.trans inf_le_left
  obtain ⟨e₁⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset O.ι V.ι
    (pushforwardStructureSheaf h) I hr e
  have e₂ : pushforwardStructureSheaf (h ∣_ V) ≅ SheafOfModules.free.{u} I :=
    (pushforwardStructureSheafRestrictIso h V).symm ≪≫ e₁
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  have : IsAffine (h ⁻¹ᵁ V).toScheme := hV.preimage h
  have : IsFinite h := IsFiniteLocallyFree.isFinite h
  obtain ⟨-, hfree⟩ :=
    module_finite_and_free_of_pushforwardStructureSheaf_iso_free (h ∣_ V) I e₂
  have hflt : IsZariskiLocalAtTarget (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) :=
    isFiniteLocallyFree_isZariskiLocalAtTarget
  have hcompV : PseudoCoherent ((h ∣_ V) ≫ f.resLE U V hle) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    exact IsZariskiLocalAtSource.resLE _ hcomp
  exact pseudoCoherent_of_comp_surjective_finiteLocallyFree_of_isAffine (h ∣_ V)
    (f.resLE U V hle) (IsZariskiLocalAtTarget.restrict hsu V)
    (IsZariskiLocalAtTarget.restrict hflf V) hfree hcompV

end AlgebraicGeometry

end
