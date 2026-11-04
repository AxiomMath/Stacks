module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartSplitLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverValuativeExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FibreRankUnique

/-!
# The image of the cover of Stacks 089J contains the minimal-degree open

The cover `ψ : X' ⟶ X` of [Stacks, Tag 089J] is **not** surjective in general: a point of `X`
whose fibre in the chart has fewer than `d` points admits no lift to the complement of the
diagonals in the `d`-fold self-product, over any extension of its residue field. What the
source's construction does prove at this stage, and what its induction on the fibre degree then
consumes, is that the image of `ψ` contains the open `U ⊆ |X|` on which the fibre degree of the
chart equals `d`.

This file proves that. The restriction of `ψ` to the scheme-theoretically dense open
`V ⊆ X'` is the `i`-th projection of the complement of the diagonals followed by the chart, by
`AlgebraicGeometry.Space.yoneda_map_chowDenseIncl_comp`, so the image of `ψ` contains the image
of that composite; and a point of `U` lies in the latter by
`AlgebraicGeometry.Space.SpacesEtale.mem_range_pointsMap_diagonalComplementProj_comp`, because
over `U` the fibre of the chart is finite locally free of rank `d`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.mem_range_pointsMap_diagonalComplementProj_comp_of_mem`:
  a point of `X` at which the chart base change is finite locally free of rank `m + 1` — read
  through the characterisation of the minimal-degree locus of
  `AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'` — lies in the
  image of the `i`-th projection of the complement of the diagonals followed by the chart.
* `AlgebraicGeometry.Space.subset_range_pointsMap_chowCoverHom`: **the image of the cover of
  [Stacks, Tag 089J] contains the minimal-degree open.** This is the hypothesis `hcov` of
  `AlgebraicGeometry.Space.hasChowSchemeCover_of_isProper_pair` for the first of its two
  morphisms.

## Implementation notes

The hypothesis `hU` is the first clause of
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'` verbatim, so
that the two compose without an intermediate reformulation. Only its right-to-left direction is
used: from `Set.range (pointsMap … ξ) ⊆ U` for a field-valued point `ξ` of `X` the rank of the
fibre is `m + 1`. The left-to-right direction, which is what shows the locus to be exactly where
the degree is maximal, is not needed here.

The base change of the chart along a field-valued point is taken in the canonical representable
form supplied by `CategoryTheory.Functor.relativelyRepresentable.pullback`, the chart being
relatively representable because it is étale.

## What is and is not proved

[Stacks, Tag 089J] is **not** proved here and no declaration in this file carries a Stacks
attribute. Surjectivity of a morphism of algebraic spaces is Stacks 03ME, carried by
`AlgebraicGeometry.Space.IsSurjective`, and **it is not proved**: what is proved is an
inclusion of the minimal-degree open in the image, which is strictly weaker and is all the
source's construction gives before the induction. Properness and H-quasi-projectivity of the
cover are untouched; they are
`AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom`.

Nothing here produces the open `U`, the degree `m + 1`, or the complementary stratum; the first
two come from
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'` and the
induction over the third is not performed.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-- **A point of the minimal-degree locus lies in the image of the complement of the diagonals.**

The hypothesis `hU` is the characterisation of the minimal-degree locus produced by
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'`: a morphism
into `X` has chart base change finite locally free of rank `m + 1` exactly when its image on
points lies in `U`. Applied to a field-valued point of `X` inside `U`, whose image on points is
that single point, it says the fibre of the chart there is finite locally free of rank `m + 1`;
and then
`AlgebraicGeometry.Space.SpacesEtale.mem_range_pointsMap_diagonalComplementProj_comp` lifts the
point to the complement of the diagonals after a finite separable extension of its residue
field. -/
theorem mem_range_pointsMap_diagonalComplementProj_comp_of_mem
    (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (m : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) (m + 1) hsep)).obj)
    (U : Set (points B S hS X.obj))
    (hU : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X.obj),
      IsAlgebraicSpace B S hS T →
      ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
        IsPullback pr₁ pr₂ c hm →
        ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} (m + 1))
            (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
          Set.range (pointsMap B S hS T hm) ⊆ U))
    (i : Fin (m + 1)) (x : points B S hS X.obj) (hx : x ∈ U) :
    x ∈ Set.range (pointsMap B S hS (yoneda.obj V)
      (yoneda.map (diagonalComplementProj B S hS X W c hc hsep (m + 1) V e i) ≫ c)) := by
  classical
  -- a field-valued representative of the point, and the morphism it presents
  obtain ⟨p, hp⟩ := Quot.exists_rep x
  set ξ : yoneda.obj p.siteObject ⟶ X.obj := yonedaEquiv.symm p.value with hξ
  have hxval : ∀ z, pointsMap B S hS (yoneda.obj p.siteObject) ξ z = x := fun z ↦
    (FieldValuedPoint.pointsMap_eq_class B S hS p z).trans hp
  -- the base change of the chart along that point, in its canonical representable form
  have hcp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c :=
    (isEtale_iff_presheaf_of_yoneda B S hS c).1 hc
  have hsq : IsPullback (yoneda.map (hcp.rep.fst' ξ)) (yoneda.map (hcp.rep.snd ξ)) c ξ :=
    hcp.rep.isPullback' ξ
  -- over `U` the fibre of the chart has rank `m + 1`
  have hflf : (MorphismProperty.inverseImage
      (IsFiniteLocallyFreeOfRank.property.{u} (m + 1))
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (hcp.rep.snd ξ)) :=
    (hU (yoneda.obj p.siteObject) ξ (isAlgebraicSpace_yoneda B S hS p.siteObject)
      (yoneda.obj (hcp.rep.pullback ξ)) (yoneda.map (hcp.rep.fst' ξ))
      (yoneda.map (hcp.rep.snd ξ)) hsq).2 (by
        rintro y ⟨z, rfl⟩
        rw [hxval z]
        exact hx)
  have hid : IsPullback (𝟙 (yoneda.obj (hcp.rep.pullback ξ)))
      (yoneda.map (hcp.rep.snd ξ)) (yoneda.map (hcp.rep.snd ξ))
      (𝟙 (yoneda.obj p.siteObject)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hrank : IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (hcp.rep.snd ξ)) (m + 1) :=
    isFiniteLocallyFreeOfRank_of_presheaf B S hS hflf (𝟙 _) (𝟙 _) (hcp.rep.snd ξ) hid
  have h := mem_range_pointsMap_diagonalComplementProj_comp B S hS X W c hc hsep m V e
    p.contained p.toBase ξ (hcp.rep.pullback ξ) (hcp.rep.snd ξ) (hcp.rep.fst' ξ) hsq hrank i
  have hxval' : pointsMap B S hS (yoneda.obj (siteObject B S hS p.contained p.toBase)) ξ
      (fieldSpecPoint B S hS p.contained p.toBase) = x := hxval _
  rwa [hxval'] at h

end SpacesEtale

/-! ### The image of the glued morphism -/

/-- **The image of the cover of [Stacks, Tag 089J] contains the minimal-degree open.**

The data `ρ`, `ψ` with the properties `hρ` and `hψ` is what
`AlgebraicGeometry.Space.exists_chowCoverHom` produces, so `ψ` is the glued morphism
`X' ⟶ X` of [Stacks, Tag 089J]; the hypothesis `hU` is the characterisation of the
minimal-degree locus of
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'`.

The restriction of `ψ` to the dense open `V ⊆ X'` is the `i`-th projection of the complement of
the diagonals followed by the chart, by
`AlgebraicGeometry.Space.yoneda_map_chowDenseIncl_comp`, so the image of `ψ` on points contains
the image of that composite, which contains `U` by
`AlgebraicGeometry.Space.SpacesEtale.mem_range_pointsMap_diagonalComplementProj_comp_of_mem`.

This is exactly the hypothesis `hcov` of
`AlgebraicGeometry.Space.hasChowSchemeCover_of_isProper_pair` for the first of its two
morphisms. Surjectivity of `ψ` onto all of `X` is **false** in general and is not claimed. -/
theorem subset_range_pointsMap_chowCoverHom (X : AlgebraicSpaces B S hS)
    (Wch : BigFppfOver B S hS) (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ)
    (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (U : Set (points B S hS X.obj))
    (hU : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X.obj),
      IsAlgebraicSpace B S hS T →
      ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj Wch) (pr₂ : Pp ⟶ T),
        IsPullback pr₁ pr₂ c hm →
        ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} (n + 1))
            (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
          Set.range (pointsMap B S hS T hm) ⊆ U))
    (ρ : ∀ i : Fin (n + 1), preimageObj B S hS
      (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
      (chowProj B S hS X Wch c hc hsep Yo j n V e)
      (chartOpensRange B S hS j hj) i ⟶ Wch)
    (hρ : ∀ i, chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫ ρ i =
      SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i)
    (ψ : yoneda.obj (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj) ⟶ X.obj)
    (hψ : ∀ i, yoneda.map (chowCoverIncl B S hS X Wch c hc hsep Yo j n V e hj i) ≫ ψ =
      yoneda.map (ρ i) ≫ c)
    (i : Fin (n + 1)) :
    U ⊆ Set.range (pointsMap B S hS
      (yoneda.obj (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj)) ψ) := by
  intro x hx
  obtain ⟨y, hy⟩ := SpacesEtale.mem_range_pointsMap_diagonalComplementProj_comp_of_mem
    B S hS X Wch c hc hsep n V e U hU i x hx
  refine ⟨pointsMap B S hS (yoneda.obj V)
    (yoneda.map (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i)) y, ?_⟩
  rw [← hy, ← Function.comp_apply (f := pointsMap B S hS
      (yoneda.obj (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj)) ψ),
    ← pointsMap_comp B S hS (yoneda.obj V)
      (yoneda.map (chowDenseIncl B S hS X Wch c hc hsep Yo j n V e hj i)) ψ,
    yoneda_map_chowDenseIncl_comp B S hS X Wch c hc hsep Yo j n V e hj ρ hρ ψ hψ i]

end AlgebraicGeometry.Space

end
