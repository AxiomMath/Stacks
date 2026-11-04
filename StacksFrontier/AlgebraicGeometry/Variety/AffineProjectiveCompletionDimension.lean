module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion

/-!
# A projective completion of an affine scheme of finite type over a field, of the same dimension

Let `K` be a field and `Y` an affine scheme locally of finite type over `K`. The scheme-theoretic
image `Y'` of a quasi-compact immersion `Y ⟶ 𝐏ⁿ_K` over `K` is projective over `K`, `Y ⟶ Y'` is a
dense open immersion ([Stacks, Tag 01RG]), and `dim(Y') = dim(Y)` ([Stacks, Tag 0A21]). This is
the projective completion used in the proof of [Stacks, Tag 0F1H].

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_isProper_topologicalKrullDim_eq_of_isAffine`: an
  affine scheme of finite type over a field is a dense open subscheme of a projective scheme of
  the same dimension.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **An affine scheme of finite type over a field is a dense open subscheme of a projective
scheme of the same dimension.** Let `K` be a field and `Y` an affine scheme locally of finite type
over `K`. There are a scheme `Y'` projective over `K` and a dense open immersion `ι : Y ⟶ Y'` over
`K` with `dim(Y') = dim(Y)`; `Y'` is the scheme-theoretic closure of `Y` in some `𝐏ⁿ_K`. -/
theorem exists_isOpenImmersion_isProper_topologicalKrullDim_eq_of_isAffine (K : Type u) [Field K]
    {Y : Scheme.{u}} [IsAffine Y] (sY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType sY] :
    ∃ (Y' : Scheme.{u}) (ι : Y ⟶ Y') (sY' : Y' ⟶ Spec (.of K)),
      IsOpenImmersion ι ∧ ι ≫ sY' = sY ∧ IsProjectiveMorphism sY' ∧ IsProper sY' ∧
        IsDominant ι ∧ topologicalKrullDim Y' = topologicalKrullDim Y := by
  obtain ⟨n, i, hi, hqc, hif⟩ := isHQuasiProjective_of_isAffine_toSpec sY
  have : IsImmersion i := hi
  have : QuasiCompact i := hqc
  have : IsOpenImmersion i.toImage := isOpenImmersion_toImage i (Or.inl hqc)
  let sY' := i.imageι ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
  have hι : i.toImage ≫ sY' = sY := by rw [← Category.assoc, Scheme.Hom.toImage_imageι, hif]
  have hproj : IsProjectiveMorphism sY' := ⟨n, i.imageι, inferInstance, rfl⟩
  have : IsProper sY' := isProper_of_isProjectiveMorphism sY' hproj
  have : IsLocallyNoetherian i.image := LocallyOfFiniteType.isLocallyNoetherian sY'
  have : CompactSpace i.image := QuasiCompact.compactSpace_of_compactSpace sY'
  have : IsNoetherian i.image := IsNoetherian.mk
  have hdom : IsDominant i.toImage := isDominant_toImage i (Or.inl hqc)
  exact ⟨i.image, i.toImage, sY', inferInstance, hι, hproj, inferInstance, hdom,
    le_antisymm (Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion K
      i.toImage sY sY' hι hdom.denseRange)
      i.toImage.isOpenEmbedding.isInducing.topologicalKrullDim_le⟩

end AlgebraicGeometry
