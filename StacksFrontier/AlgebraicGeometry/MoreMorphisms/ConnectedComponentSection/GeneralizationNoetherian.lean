module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Reduced
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.GeneralizationOverDvr
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation

/-!
# Stability of the locus `X⁰` under generalization over a locally Noetherian source

Let `f : X ⟶ Y` be flat and of finite presentation with a specified section `s`, as in
Situation 055L, and assume the source `X` is locally Noetherian. If a point `x` whose fibre is
geometrically reduced lies in the locus `X⁰`, then so does every generalization of `x`.

This is the reduction of the stability of `X⁰` under generalization to a discrete valuation
ring base, the second step of the proof of Stacks Tag 055Q: Stacks Tag 054F presents the
specialization as the image of the generic-to-closed specialization on the spectrum of a
discrete valuation ring `R`, the sectioned situation is base changed along the resulting
morphism `Spec R ⟶ X ⟶ Y`, and Stacks Tag 055M identifies the locus upstairs with the inverse
image of `X⁰`.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_of_isLocallyNoetherian`:
  the locally Noetherian case of the stability of `X⁰` under generalization.

## Implementation notes

Geometric reducedness is needed only for the one fibre containing `x`, and is expressed as
`AlgebraicGeometry.GeometricallyReduced` of `Scheme.Hom.fiberToSpecResidueField`; this is the
form which Stacks Tag 0576 transports along the base change. The hypothesis cannot be
strengthened to geometric reducedness of all the fibres of `f`: a morphism obtained from a
cofiltered limit of affine bases has geometrically reduced fibres only over the image of the
projection from the limit, and that projection is not surjective, so the global property does
not descend to the stages of such a limit while the property at one point does.

The morphism `Spec R ⟶ X` of Tag 054F lifts to a section-like morphism of the base change, whose
values at the closed and the generic point of `Spec R` are the two points to which the discrete
valuation ring case is applied.

## References

* [Stacks Project, Tag 054F](https://stacks.math.columbia.edu/tag/054F)
* [Stacks Project, Tag 055L](https://stacks.math.columbia.edu/tag/055L)
* [Stacks Project, Tag 055M](https://stacks.math.columbia.edu/tag/055M)
* [Stacks Project, Tag 0576](https://stacks.math.columbia.edu/tag/0576)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

/-- The generic point of the spectrum of a domain is the zero ideal. -/
private theorem genericPoint_spec_eq_bot (R : Type u) [CommRing R] [IsDomain R] :
    genericPoint (Spec (CommRingCat.of R)) = (⟨⊥, inferInstance⟩ : PrimeSpectrum R) := by
  refine (genericPoint_spec (Spec (CommRingCat.of R))).eq ?_
  show closure {(⟨⊥, inferInstance⟩ : PrimeSpectrum R)} = Set.univ
  rw [PrimeSpectrum.closure_singleton]
  simp

/-- **The locally Noetherian case of Stacks Tag 055Q.** Let `f : X ⟶ Y` be flat and of finite
presentation with a section `s`, and let `X` be locally Noetherian. If `x` lies in the locus
`X⁰` and the fibre through `x` is geometrically reduced, then every point specializing to `x`
lies in `X⁰`. -/
theorem mem_locus_of_specializes_of_isLocallyNoetherian (D : ConnectedAlongSection.{u})
    (hfp : FinitePresentation D.f) [Flat D.f] [IsLocallyNoetherian D.X] {x x' : D.X}
    (hgr : GeometricallyReduced (D.f.fiberToSpecResidueField (D.f x)))
    (hx : x ∈ D.locus) (hspec : x' ⤳ x) : x' ∈ D.locus := by
  obtain ⟨R, hR, hDom, hDVR, g, hgη, hgc⟩ := exists_dvr_morphism_of_specializes D.X hspec
  obtain ⟨σ, hσ⟩ : ∃ p : ↥(Spec (CommRingCat.of R)), p = IsLocalRing.closedPoint R := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ :
      ∃ p : ↥(Spec (CommRingCat.of R)), p = (⟨⊥, inferInstance⟩ : PrimeSpectrum R) := ⟨_, rfl⟩
  have hgcσ : g σ = x := by rwa [hσ]
  have hgηη : g η = x' := by rwa [hη, ← genericPoint_spec_eq_bot R]
  have hspecση : η ⤳ σ := by
    subst hσ hη
    exact IsLocalRing.specializes_closedPoint _
  let h : Spec (CommRingCat.of R) ⟶ D.Y := g ≫ D.f
  let fR : pullback D.f h ⟶ Spec (CommRingCat.of R) := pullback.snd D.f h
  let pr : pullback D.f h ⟶ D.X := pullback.fst D.f h
  have hPB : IsPullback pr fR D.f h := IsPullback.of_hasPullback D.f h
  -- The base change of the sectioned situation along `Spec R ⟶ X ⟶ Y`.
  let sR : Spec (CommRingCat.of R) ⟶ pullback D.f h := pullback.lift (h ≫ D.s) (𝟙 _) (by
    rw [Category.assoc, D.section_fac, Category.comp_id, Category.id_comp])
  have hsecR : sR ≫ fR = 𝟙 (Spec (CommRingCat.of R)) := pullback.lift_snd _ _ _
  let DR : ConnectedAlongSection.{u} :=
    ⟨pullback D.f h, Spec (CommRingCat.of R), fR, sR, hsecR⟩
  have hlocus : DR.locus = pr ⁻¹' D.locus :=
    locus_eq_preimage_of_isPullback D DR pr h hPB (pullback.lift_fst _ _ _)
  -- The morphism `Spec R ⟶ X` lifts to the base change.
  have htcond : g ≫ D.f = 𝟙 (Spec (CommRingCat.of R)) ≫ h := (Category.id_comp h).symm
  let t : Spec (CommRingCat.of R) ⟶ pullback D.f h := pullback.lift g (𝟙 _) htcond
  have htpr : ∀ p, pr (t p) = g p := fun p => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  have htf : ∀ p, fR (t p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]; rfl
  -- Finite presentation and flatness pass to the base change.
  have hfpR : FinitePresentation fR :=
    ⟨MorphismProperty.of_isPullback hPB hfp.1, MorphismProperty.of_isPullback hPB hfp.2.1,
      MorphismProperty.of_isPullback hPB hfp.2.2⟩
  have hflatR : Flat fR := MorphismProperty.of_isPullback hPB inferInstance
  -- Geometric reducedness of the relevant fibre passes to the base change.
  have hredR : IsReduced (fR.fiber σ) := by
    refine isReduced_fiber_of_geometricallyReduced_fiberToSpecResidueField fR _ ?_
    have hmem : σ ∈ h ⁻¹' {y : D.Y | GeometricallyReduced (D.f.fiberToSpecResidueField y)} := by
      show GeometricallyReduced (D.f.fiberToSpecResidueField ((g ≫ D.f) σ))
      rwa [Scheme.Hom.comp_apply, hgcσ]
    rwa [← geometricallyReduced_fiber_set_eq_preimage_of_isPullback D.f fR pr h hPB] at hmem
  -- Transport the two points to the base change and apply the discrete valuation ring case.
  have hxR : t σ ∈ DR.locus := by
    rwa [hlocus, Set.mem_preimage, htpr, hgcσ]
  have hconcl : t η ∈ DR.locus :=
    mem_locus_of_specializes_over_dvr fR sR hsecR hfpR hσ hη hredR (htf σ) (htf η) hxR
      (hspecση.map t.continuous)
  rwa [hlocus, Set.mem_preimage, htpr, hgηη] at hconcl

end ConnectedAlongSection

end AlgebraicGeometry

end
