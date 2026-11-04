module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonSheafCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSmallEtalePullbackSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtalePullback

/-!
# The sheaf conditions satisfied by `π_X⁻¹F` (Stacks 0DG7)

Let `T` be a big étale site of algebraic spaces over `S`, `X` an algebraic space of it and `F` a
sheaf on the spaces-étale site of `X`. Stacks 0DG7 says that `π_X⁻¹F` is given by the rule
`(π_X⁻¹F)(Y) = Γ(Y_étale, f_small⁻¹F)` (this is
`AlgebraicGeometry.BigEtaleSpaceSite.bigToSmall_inverseImageSectionsIso`) and that it satisfies
the sheaf condition for smooth, syntomic, fppf, fpqc and ph coverings. This file proves the
sheaf condition for smooth, syntomic, fppf and fpqc coverings, and records the ph clause, which
is `AlgebraicGeometry.BigPHSpaceSite.isSheaf_bigToSmallEtale_inverseImage`
(`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSmallEtalePullbackSheaf`).

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.inverseImage_isSheafFor_smooth_syntomic_fppf_fpqc` — the
  sheaf condition for smooth, syntomic, fppf and fpqc coverings.
* `AlgebraicGeometry.BigPHSpaceSite.isSheaf_bigToSmallEtale_inverseImage` — the ph sheaf
  condition: for a big ph site `P` of algebraic spaces built on the same big fppf site as the big
  étale site `E`, `π_X⁻¹F`, read on the big ph slice at `X` (Stacks 0DFL), is a sheaf for the ph
  topology of `X`.

## Implementation notes

Each sheaf condition is stated for every family of the slice of algebraic spaces over `X` whose
underlying family of algebraic spaces is a covering of the topology in question, as in
`StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonSheafCondition`; no chosen big site for
the finer topology is involved. The fpqc clause,
`AlgebraicGeometry.BigEtaleSpaceSite.inverseImage_isSheafFor_of_isFpqcCovering`
(`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSheaf`), is Cases I–III of the
Stacks proof: étale
descent (`AlgebraicGeometry.BigEtaleSpaceSite.isEtaleSheafOver_inverseImage`) and descent for
finite affine fpqc coverings of affine schemes
(`AlgebraicGeometry.BigEtaleSpaceSite.isAffineFpqcSheafOver_inverseImage`, from Stacks 09XN),
assembled by `AlgebraicGeometry.Space.isSheafFor_of_isFpqcCovering`. The smooth, syntomic and
fppf clauses follow from the fpqc one, since such coverings are fpqc coverings (Stacks 0DFQ).

The ph clause: by the ph sheaf criterion (Stacks 0DFM) it amounts to étale
descent together with descent along proper surjective morphisms of algebraic spaces, and the
latter is full faithfulness of descent of small étale sheaves along a proper surjection
(`AlgebraicGeometry.Space.isPrestackFor_of_isProper_isSurjective`), whose scheme case
`AlgebraicGeometry.Space.properSurjectivePrestackOverSchemes` comes from proper base change in
degree zero (Stacks 0A3U). The ph topology lives on the slices of a big ph site of algebraic
spaces, so the clause is stated there, for any such site sharing the big fppf site of `E`.

## References

* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) (X : T.Spaces)
  (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1)))

/-- **Stacks 0DG7, the sheaf conditions for smooth, syntomic, fppf and fpqc coverings.** Let `F`
be a sheaf on the spaces-étale site of `X`. Then `π_X⁻¹F` satisfies the sheaf condition for
every family of the slice over `X` whose underlying family of algebraic spaces is a smooth,
syntomic, fppf or fpqc covering. -/
@[stacks 0DG7 "Moreover: the sheaf condition for smooth, syntomic, fppf and fpqc coverings"]
theorem inverseImage_isSheafFor_smooth_syntomic_fppf_fpqc :
    (∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      Space.IsSmoothCovering T.fppfSite S T.fppf_mem
        (fun i ↦ ((E.map (Over.forget X)).X i).obj) (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
      Presieve.IsSheafFor ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj E.presieve₀) ∧
    (∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      Space.IsSyntomicCovering T.fppfSite S T.fppf_mem
        (fun i ↦ ((E.map (Over.forget X)).X i).obj) (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
      Presieve.IsSheafFor ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj E.presieve₀) ∧
    (∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      Space.IsFppfCovering T.fppfSite S T.fppf_mem
        (fun i ↦ ((E.map (Over.forget X)).X i).obj) (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
      Presieve.IsSheafFor ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj E.presieve₀) ∧
    (∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      Space.IsFpqcCovering T.fppfSite S T.fppf_mem (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
      Presieve.IsSheafFor ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj E.presieve₀) := by
  have hfpqc : ∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      Space.IsFpqcCovering T.fppfSite S T.fppf_mem (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
      Presieve.IsSheafFor ((bigToSmallEtaleMorphism T X).inverseImage.obj F).obj E.presieve₀ :=
    fun _ E hE ↦ inverseImage_isSheafFor_of_isFpqcCovering T X F E.f hE
  exact ⟨fun _ E hE ↦ Space.isSheafFor_smoothCovering_of_isSheafFor_fpqcCoverings _ _ _ hfpqc E hE,
    fun _ E hE ↦ Space.isSheafFor_syntomicCovering_of_isSheafFor_fpqcCoverings _ _ _ hfpqc E hE,
    fun _ E hE ↦ Space.isSheafFor_fppfCovering_of_isSheafFor_fpqcCoverings _ _ _ hfpqc E hE,
    hfpqc⟩

end AlgebraicGeometry.BigEtaleSpaceSite

/- **Stacks 0DG7, the ph sheaf condition.** For a big ph site `P` of algebraic spaces and a big
étale site `E` built on the same big fppf site, an algebraic space `X` of `P` and a sheaf `G` on
the spaces-étale site of `X`, the presheaf `π_X⁻¹G`, read on the big ph slice at `X`, is a sheaf
for the ph topology of `X`. -/
add_to_stacks 0DG7 "Moreover: the sheaf condition for ph coverings"
  AlgebraicGeometry.BigPHSpaceSite.isSheaf_bigToSmallEtale_inverseImage

end
