module

public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOriginIntersection
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# A non-affine morphism whose source is an affine scheme

A morphism of schemes whose source *and* target are affine is affine, so a non-affine morphism
needs a non-affine target. It does **not** need a non-affine source: an affine chart of affine
space with its origin doubled is an affine scheme, and in dimension greater than one its
inclusion is not an affine morphism, because the preimage of the other chart is the punctured
affine space.

## Main results

* `AlgebraicGeometry.not_isAffineHom_chartInclusion`: in dimension greater than one, neither
  chart inclusion of affine space with doubled origin is an affine morphism.
* `AlgebraicGeometry.compactSpace_affineSpaceWithDoubledZero` and
  `AlgebraicGeometry.quasiSeparatedSpace_affineSpaceWithDoubledZero`: affine space with doubled
  origin is quasi-compact and quasi-separated, so it is a legal base for the limit statements of
  Stacks Tags 09ZM and 09ZN.

## Implementation notes

The non-affineness of the chart intersection is
`AlgebraicGeometry.not_isAffineOpen_chartIntersection`. Turning it into a statement about the
*preimage* of one chart under the other avoids recomputing that preimage: the chart inclusion is
an open immersion, so its image of the preimage is the intersection of the two chart ranges
(`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`) and the preimage is isomorphic
to that image as a scheme (`AlgebraicGeometry.Scheme.Hom.isoImage`).

Quasi-compactness is read off the two-chart cover, each chart being an affine open and therefore
quasi-compact. Quasi-separatedness is read off the same cover through
`AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover`, whose remaining hypothesis is the
quasi-compactness of each pairwise intersection of charts; rather than identify that intersection
with the punctured affine space, the proof uses that the charts are spectra of a polynomial ring
in finitely many variables over a field, hence Noetherian spaces, in which *every* subset is
quasi-compact.

The purpose of all three results is Stacks Tag 09ZM at an index universe independent of the
scheme universe, whose refutation needs a system of qcqs schemes over a qcqs base with affine
transition morphisms, an affine morphism from the limit, and a stage whose structure morphism is
not affine. The last ingredient is what
`AlgebraicGeometry.not_isAffineHom_chartInclusion` supplies, and the other two make the doubled
origin a legal base. Note that the stage here is an *affine scheme*: a non-affine structure
morphism does not require a non-affine stage, only a non-affine base, and Tag 09ZM does not ask
the base to be affine. No Stacks Tag 09ZM attribute is attached anywhere in this file: nothing
here states Tag 09ZM or its negation, and the system realising the refutation is not built here.

## References

* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
* [Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01JD.** In dimension greater than one, a chart inclusion of affine
space with doubled origin is not an affine morphism, even though its source is an affine scheme:
the preimage of the other chart is the punctured affine space, which is not affine. -/
theorem not_isAffineHom_chartInclusion (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    ¬ IsAffineHom (chartInclusion k n 0) := by
  intro h
  refine not_isAffineOpen_chartIntersection k n hn ?_
  have hV : IsAffineOpen (chartInclusion k n 1).opensRange := isAffineOpen_opensRange _
  have hpre : IsAffineOpen (chartInclusion k n 0 ⁻¹ᵁ (chartInclusion k n 1).opensRange) :=
    IsAffineHom.isAffine_preimage _ hV
  have himage : chartInclusion k n 0 ''ᵁ
      (chartInclusion k n 0 ⁻¹ᵁ (chartInclusion k n 1).opensRange) =
      (chartInclusion k n 0).opensRange ⊓ (chartInclusion k n 1).opensRange :=
    (chartInclusion k n 0).image_preimage_eq_opensRange_inf _
  have e := (chartInclusion k n 0).isoImage
    (chartInclusion k n 0 ⁻¹ᵁ (chartInclusion k n 1).opensRange)
  have hIm : IsAffine
      (chartInclusion k n 0 ''ᵁ
        (chartInclusion k n 0 ⁻¹ᵁ (chartInclusion k n 1).opensRange)).toScheme :=
    (IsAffine.iff_of_isIso e.hom).mp hpre
  exact himage ▸ hIm

/-- The two chart inclusions cover affine space with doubled origin. -/
theorem iSup_opensRange_chartInclusion (k : Type u) [Field k] (n : ℕ) :
    ⨆ i : Fin 2, (chartInclusion k n i).opensRange = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨i, y, hy⟩ := (doubledZeroGlueData k n).ι_jointly_surjective x
  exact Opens.mem_iSup.2 ⟨i.down, y, hy⟩

/-- Affine space with doubled origin is quasi-compact: it is covered by its two affine
charts. -/
instance compactSpace_affineSpaceWithDoubledZero (k : Type u) [Field k] (n : ℕ) :
    CompactSpace (affineSpaceWithDoubledZero k n) := by
  rw [← isCompact_univ_iff, ← Opens.coe_top, ← iSup_opensRange_chartInclusion k n]
  rw [Opens.coe_iSup]
  refine isCompact_iUnion fun i ↦ ?_
  exact (isAffineOpen_opensRange (chartInclusion k n i)).isCompact

/-- Affine space with doubled origin is quasi-separated: it has a cover by two affine charts,
and each pairwise intersection of charts is the image of a subset of a Noetherian space, in which
every subset is quasi-compact. -/
instance quasiSeparatedSpace_affineSpaceWithDoubledZero (k : Type u) [Field k] (n : ℕ) :
    QuasiSeparatedSpace (affineSpaceWithDoubledZero k n) := by
  refine Scheme.quasiSeparatedSpace_of_isOpenCover
    (fun i : Fin 2 ↦ (chartInclusion k n i).opensRange)
    (IsOpenCover.mk (iSup_opensRange_chartInclusion k n))
    (fun i ↦ isAffineOpen_opensRange _) fun i j ↦ ?_
  rw [← TopologicalSpace.Opens.coe_inf,
    ← (chartInclusion k n i).image_preimage_eq_opensRange_inf
      ((chartInclusion k n j).opensRange), Scheme.Hom.coe_image]
  have hnoeth : TopologicalSpace.NoetherianSpace
      (Spec (.of (MvPolynomial (Fin n) k))) :=
    inferInstanceAs
      (TopologicalSpace.NoetherianSpace (PrimeSpectrum (MvPolynomial (Fin n) k)))
  exact (hnoeth.isCompact _).image (chartInclusion k n i).continuous

end AlgebraicGeometry

end
