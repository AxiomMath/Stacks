module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverValuativeExistence

/-!
# The cover of Stacks 089J is proper

The morphism `ψ : X' ⟶ X` of Stacks 089J is proper. The source checks this by the refined
valuative criterion of Stacks 089G, which
`AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion` applies for the pair
`V ⟶ X' ⟶ X`, and whose seven hypotheses are now all available:

* quasi-compactness of `ψ`, quasi-separatedness of `ψ`, locally of finite type for `ψ`, and the
  uniqueness clause are the four formal consequences of
  `StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSeparated` of the shape `ψ` has — its
  source is an object of the site H-quasi-projective over the base;
* quasi-compactness of `V ⟶ X'` is the same file's
  `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_compactSpace`;
* density of the image of `V` on points is
  `AlgebraicGeometry.Space.denseRange_pointsMap_yoneda_map_of_comp_isOpenImmersion`, whose
  dominance hypothesis is assembled here out of
  `AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_toImage` and quasi-compactness
  of the morphism into the fibre power;
* the valuative lifting condition is
  `AlgebraicGeometry.Space.exists_dominatingExtension_lift_chowCover`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.denseToImage_toScheme`: the morphism of schemes underlying
  `AlgebraicGeometry.Space.denseToImage` is the morphism onto the scheme-theoretic image.
* `AlgebraicGeometry.Space.isDominant_denseToImage`: **it is dominant**, when the morphism into
  the fibre power is quasi-compact. This is Stacks 01RG, applied.
* `AlgebraicGeometry.Space.denseRange_pointsMap_chowDenseIncl`: the dense open of the cover has
  dense image on the point set of the cover — the hypothesis `hdense` of the refined valuative
  criterion.
* `AlgebraicGeometry.Space.isProper_chowCoverHom`: **the morphism `X' ⟶ X` of Stacks 089J is
  proper.**

## What is and is not proved

Stacks 089J is **not** proved here and no declaration in this file carries a Stacks attribute:
Stacks 089G is carried by
`AlgebraicGeometry.Space.universallyClosed_of_refinedValuativeCriterion` and
`AlgebraicGeometry.Space.isSeparated_of_refinedValuativeCriterion`, Stacks 03ZM by
`AlgebraicGeometry.Space.IsProper`, Stacks 01RG by
`AlgebraicGeometry.isOpenImmersion_toImage`, Stacks 0AGC by
`AlgebraicGeometry.Space.isSeparated_of_comp`, Stacks 03KK by
`AlgebraicGeometry.Space.isQuasiSeparated_of_isSeparated` and Stacks 03KU by
`AlgebraicGeometry.Space.valuativeCriterion_uniqueness_of_isSeparated`.

**Surjectivity of the cover is not proved**, and neither is the induction on the minimal fibre
degree by which Stacks 089J passes from the cover over the open of minimal degree to a cover of
all of `X`. Properness alone is what this file delivers.

The hypotheses kept and not derived are the side conditions of the construction: that the chart
is étale, separated and surjective and the compactification proper over the base, that the
algebraic space is separated over the base, that `d = n + 1` is at least the fibre-degree bound
of Stacks 03JL (`AlgebraicGeometry.Space.exists_degreeBound_match` produces such a `d`), that
the underlying scheme of `V` is compact and the underlying scheme of `X'` quasi-separated, that
the morphism of `V` into the fibre power is quasi-compact, and that `X'` is H-quasi-projective
over the base. None of them is properness or valuative liftability of `ψ`, which is what is
proved.

## References

* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 089G](https://stacks.math.columbia.edu/tag/089G)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (Wch : BigFppfOver B S hS)
    (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.denseToImage` is the morphism
of Mathlib onto the scheme-theoretic image. -/
theorem denseToImage_toScheme :
    (BigFppfOver.toScheme B S hS).map (denseToImage B S hS X Wch c hc hsep Yo j n V e) =
      Scheme.Hom.toImage ((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)) :=
  toSchemeImageObj_toScheme B S hS _

/-- **The morphism from the dense open onto the scheme-theoretic image is dominant.** The
morphism onto a scheme-theoretic image is scheme-theoretically dominant by Stacks 01RG, and a
quasi-compact scheme-theoretically dominant morphism is dominant; quasi-compactness of the
morphism onto the image follows from quasi-compactness of the morphism into the fibre power by
cancellation, the closed immersion of the image being quasi-compact. -/
theorem isDominant_denseToImage
    (hVqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))) :
    _root_.AlgebraicGeometry.IsDominant ((BigFppfOver.toScheme B S hS).map
      (denseToImage B S hS X Wch c hc hsep Yo j n V e)) := by
  have := hVqc
  have hqc : AlgebraicGeometry.QuasiCompact (Scheme.Hom.toImage
      ((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))) := by
    have h1 : AlgebraicGeometry.QuasiCompact
        (((BigFppfOver.toScheme B S hS).map
            (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).toImage ≫
          ((BigFppfOver.toScheme B S hS).map
            (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι) := by
      rw [Scheme.Hom.toImage_imageι]
      exact hVqc
    have := h1
    exact QuasiCompact.of_comp
      (((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).toImage)
      (((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι)
  have := hqc
  have hstd : IsSchemeTheoreticallyDominant (Scheme.Hom.toImage
      ((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))) :=
    Scheme.Hom.isSchemeTheoreticallyDominant_toImage _
  have := hstd
  exact inferInstanceAs (_root_.AlgebraicGeometry.IsDominant (Scheme.Hom.toImage
    ((BigFppfOver.toScheme B S hS).map
      (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))))

variable (hj : _root_.AlgebraicGeometry.IsOpenImmersion
  ((BigFppfOver.toScheme B S hS).map j))

/-- **The inclusion of the cover of Stacks 089J into the scheme-theoretic image is an open
immersion**, being the inclusion of an open of the underlying scheme. -/
theorem isOpenImmersion_chowCoverObjι :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj)) := by
  have h : _root_.AlgebraicGeometry.IsOpenImmersion
      (unionPreimageOpens B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
        (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj)).ι :=
    inferInstance
  rw [chowCoverObjι_toScheme]
  exact h

/-- **The hypothesis `hdense` of the refined valuative criterion for the cover of Stacks
089J.** The dense open `V` has dense image on the point set of `X'`: its composite with the open
immersion `X' ⟶ Z` is the morphism onto the scheme-theoretic image, which is dominant by
`AlgebraicGeometry.Space.isDominant_denseToImage`, so
`AlgebraicGeometry.Space.denseRange_pointsMap_yoneda_map_of_comp_isOpenImmersion` applies. -/
theorem denseRange_pointsMap_chowDenseIncl
    (hVqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))) (i₀ : Fin (n + 1)) :
    letI : TopologicalSpace (points B S hS
        (yoneda.obj (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj))) :=
      pointTopology B S hS _
    DenseRange (pointsMap B S hS (yoneda.obj V)
      (yoneda.map (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i₀))) := by
  refine denseRange_pointsMap_yoneda_map_of_comp_isOpenImmersion B S hS
    (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i₀)
    (chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj)
    (isOpenImmersion_chowCoverObjι B S hS X Wch c hc hsep Yo j n V e hj) ?_
  rw [chowDenseIncl_comp_chowCoverObjι]
  exact isDominant_denseToImage B S hS X Wch c hc hsep Yo j n V e hVqc

/-- **The morphism `X' ⟶ X` of Stacks 089J is proper.**

The data is the one of Stacks 089J: a separated surjective étale chart `c : W ⟶ X` of an
algebraic space separated over the base, an open immersion `j : W ⟶ Y` into a compactification
which is proper over the base, the complement `V` of the diagonals in the `(n+1)`-fold
self-product of the chart over `X` as an object of the site, the cover
`X' = ⋃ᵢ gᵢ⁻¹(W)` inside the scheme-theoretic image of `V` in the `(n+1)`-fold fibre power of
`Y` over the base, and the morphism `ψ : X' ⟶ X` glued out of the `ρ i ≫ c`, which is what
`AlgebraicGeometry.Space.exists_chowCoverHom` produces.

Properness is checked by the refined valuative criterion of Stacks 089G in the form
`AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion`, relative to the inclusion
`AlgebraicGeometry.Space.chowDenseIncl` of the dense open. Its valuative lifting condition is
`AlgebraicGeometry.Space.exists_dominatingExtension_lift_chowCover`; the six remaining
hypotheses are formal consequences of the shape of `ψ` and of the density of `V`.

Nothing about properness or valuative liftability of `ψ` is assumed: `hmatch` is the
fibre-degree bound of Stacks 03JL, which
`AlgebraicGeometry.Space.exists_degreeBound_match` produces for a suitable `n`; the remaining
hypotheses are size and finiteness conditions on `V`, `X'` and the compactification. -/
theorem isProper_chowCoverHom
    (hcs : IsSurjective B S hS c)
    (hYo : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Yo.hom))
    (hXsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from X.obj))
    (hVqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)))
    (hVc : CompactSpace ((BigFppfOver.toScheme B S hS).obj V))
    (hX'qs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj
      (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj)))
    (hqp : IsHQuasiProjective
      (B.inclusion.map (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj).hom))
    (hmatch : ∀ (K' : Type u) (_ : Field K') (T' : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec (CommRingCat.of K'))
      (ξ : yoneda.obj T' ⟶ X.obj) (w : Fin (n + 1) → (T' ⟶ Wch)),
      (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w →
        ∀ v : T' ⟶ Wch, yoneda.map v ≫ c = ξ → ∃ k, v = w k)
    (ρ : ∀ i : Fin (n + 1), preimageObj B S hS
      (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
      (chowProj B S hS X Wch c hc hsep Yo j n V e)
      (chartOpensRange B S hS j hj) i ⟶ Wch)
    (hρ : ∀ i, chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫ ρ i =
      SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i)
    (ψ : yoneda.obj (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj) ⟶ X.obj)
    (hψ : ∀ i, yoneda.map (chowCoverIncl B S hS X Wch c hc hsep Yo j n V e hj i) ≫ ψ =
      yoneda.map (ρ i) ≫ c)
    (i₀ : Fin (n + 1)) :
    IsProper B S hS ψ :=
  isProper_of_refinedValuativeCriterion B S hS
    (isAlgebraicSpace_yoneda B S hS V)
    (isAlgebraicSpace_yoneda B S hS (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj))
    X.2 (yoneda.map (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i₀)) ψ
    (isQuasiCompact_of_isHQuasiProjective_source B S hS _ ψ hXsep hqp)
    (isQuasiCompact_yoneda_map_of_compactSpace B S hS
      (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i₀) hVc hX'qs)
    (isQuasiSeparated_of_isHQuasiProjective_source B S hS _ ψ hqp)
    (isLocallyOfFiniteType_of_isHQuasiProjective_source B S hS _ ψ X.2 hqp)
    (denseRange_pointsMap_chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj hVqc i₀)
    (fun q _ _ ↦ subsingleton_lift_of_isHQuasiProjective_source B S hS _ ψ hqp q)
    (fun q g hg ↦ exists_dominatingExtension_lift_chowCover B S hS X Wch c hc hsep hcs Yo j n V
      e hj hYo hXsep hmatch ρ hρ ψ hψ i₀ q g hg)

end AlgebraicGeometry.Space

end
