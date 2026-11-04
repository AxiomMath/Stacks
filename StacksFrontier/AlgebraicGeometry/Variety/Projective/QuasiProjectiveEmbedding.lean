module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.EmbeddingProjectiveSpaceOfModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-projective variety is an open subscheme of a closed subvariety of `𝐏(V)`

A quasi-projective variety `X` over a field `k` admits a quasi-compact immersion over `k` into
`ℙᴺ_k` (Tag 087S part (2), the base `Spec k` carrying the ample module `𝒪`). The scheme-theoretic
image `X̄` of that immersion is a closed subvariety of `ℙᴺ_k`, and `X` is an open subscheme of it.
This file records the embedding in the form the intersection chapter uses, with `ℙᴺ_k` read as
`𝐏(V) = AlgebraicGeometry.projectiveSpaceOfModule k V` for `V = kᴺ⁺¹`, as in
`AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOfModule_of_isProjectiveVariety`.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_projectiveSpaceOfModule_of_isQuasiProjectiveVariety`:
  a quasi-projective variety is, over `k`, an open subscheme of a closed subvariety of
  `𝐏(kᴺ⁺¹)` of the same dimension, for some `N`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A quasi-projective variety is an open subscheme of a closed subvariety of `𝐏(kᴺ⁺¹)`.** The
structure morphism of a quasi-projective variety is H-quasi-projective (Tag 087S part (2), over
the base `Spec k`, whose structure sheaf is ample): it factors as a quasi-compact immersion into
`ℙᴺ_k` followed by the structure morphism of `ℙᴺ_k`. The scheme-theoretic image `X̄` of that
immersion is a closed subscheme of `ℙᴺ_k`, the immersion factors through `X̄` by an open immersion,
and `X̄` is a variety because `X` is, of the same dimension because `X` is dense in it. The
standard basis of `kᴺ⁺¹` identifies `ℙᴺ_k` with `𝐏(kᴺ⁺¹)` over `k`
(`AlgebraicGeometry.basisProjectiveSpaceIso`). -/
@[ega "II 5.3.3" "special case"]
public theorem exists_isOpenImmersion_projectiveSpaceOfModule_of_isQuasiProjectiveVariety
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsQuasiProjectiveVariety k p] :
    ∃ (N : ℕ) (Xb : Scheme.{u}) (iX : Xb ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k))
      (j : X ⟶ Xb),
      IsClosedImmersion iX ∧ IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) ∧
        IsOpenImmersion j ∧
        j ≫ iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = p ∧
        topologicalKrullDim Xb = topologicalKrullDim X ∧
        Module.finrank k (Fin (N + 1) → k) = N + 1 := by
  have hqp : IsQuasiProjective p := IsQuasiProjectiveVariety.isQuasiProjective
  obtain ⟨N, i, hi, hiqc, hip⟩ := isHQuasiProjective_of_isQuasiProjective p
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of k))) hqp
  have := hi
  have := hiqc
  set g : X ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k) :=
    i ≫ (basisProjectiveSpaceIso (Pi.basisFun k (Fin (N + 1)))).hom with hg
  have hgp : g ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = p := by
    rw [hg, Category.assoc, basisProjectiveSpaceIso_hom_comp_toSpec, ← hip]
    rfl
  have : IsVariety k p := inferInstance
  have : IsIntegral g.image := Stacks.Chow.isIntegral_image g
  have : IsProper (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) :=
    ProjectiveSpaceOfModule.isProper_projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)
  have hcomp : g.toImage ≫ g.imageι ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = p := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hgp]
  have : IsLocallyNoetherian g.image := LocallyOfFiniteType.isLocallyNoetherian
    (g.imageι ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
  have : CompactSpace g.image := QuasiCompact.compactSpace_of_compactSpace
    (g.imageι ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
  have : IsNoetherian g.image := ⟨⟩
  refine ⟨N, g.image, g.imageι, g.toImage, inferInstance, IsVariety.mk, inferInstance, hcomp,
    le_antisymm ?_ g.toImage.isOpenEmbedding.isInducing.topologicalKrullDim_le,
    Module.finrank_fin_fun k⟩
  exact Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion k
    g.toImage p (g.imageι ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) hcomp
    g.toImage.denseRange

end AlgebraicGeometry
