module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ConstructionDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverMinimalDegreeImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverQuasiProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSideConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalDegreeFibreBound
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The cover of the minimal-degree stratum of Stacks 089J

This file performs the construction of [Stacks, Tag 089J] once, for a given affine surjective
étale chart of a separated algebraic space of finite type over `Spec A`, and discharges every
side condition of it. What comes out is a scheme `X'` in the site, H-quasi-projective over
`Spec A`, together with a **proper** morphism `X' ⟶ X` whose image contains the nonempty open
`U ⊆ |X|` on which the fibre degree of the chart is largest — together with the strict drop of
that degree off `U`, which is what the induction of [Stacks, Tag 089J] recurses on.

That is the whole of the tag's construction except the induction: the morphism produced here is
*not* surjective, and cannot be, because a point of `|X| ∖ U` has fewer than `d` preimages in
the chart and so no lift to the complement of the diagonals over any extension of its residue
field.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_chowCover_minimalDegreeOpen`: **the cover of the
  minimal-degree stratum.** For an algebraic space separated and of finite type over `Spec A`
  with a nonempty point set and an affine surjective étale chart, there are a degree `d` and a
  nonempty open `U` of the point set, with `d` positive and characterised as the degree of the
  chart base change exactly over `U`, such that `X` is covered over `U` by a proper morphism
  from a scheme H-quasi-projective over `Spec A`, such that the chart base change along any
  morphism whose image misses `U` has degree strictly less than `d`, and such that every fibre
  of the chart at a field-valued point has degree at most `d`.

## Implementation notes

Every hypothesis of
`AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom` is discharged here:

* separatedness of the chart as a morphism, from affineness of the chart and Stacks 03FZ;
* the compactification `Y`, from
  `AlgebraicGeometry.Space.exists_compactificationObj_of_isAffine`;
* compactness of the complement `V` of the diagonals, from
  `AlgebraicGeometry.Space.SpacesEtale.compactSpace_of_iso_underlying_diagonalComplement`,
  whose two inputs are quasi-compactness of `X` over the base — which finite type gives — and
  quasi-compactness of the chart, which is
  `AlgebraicGeometry.Space.isQuasiCompact_of_compactSpace_source`;
* quasi-compactness of `V ⟶ Y ×_A ⋯ ×_A Y`, because `V` is compact and the fibre power is a
  quasi-separated space, being H-projective over `Spec A`;
* quasi-separatedness of the underlying space of the cover, likewise, because the cover is
  H-quasi-projective over `Spec A` by
  `AlgebraicGeometry.Space.isHQuasiProjective_chowCoverObj_hom`;
* the fibre-exhaustion clause, from
  `AlgebraicGeometry.Space.exists_eq_of_minimalDegreeOpen`;
* the glued morphism `ψ` and the maps `ρ`, from
  `AlgebraicGeometry.Space.exists_chowCoverHom`.

That the minimal fibre degree is positive — so that the self-product can be written with `n + 1`
factors — is proved rather than assumed: over a point of `U` the fibre of the chart has degree
`d`, and it is nonempty because the chart is surjective, so `d = 0` is impossible by
`Stacks.Morphisms.isEmpty_of_isFiniteLocallyFreeOfRank_zero_of_specTarget`.

## What is and is not proved

[Stacks, Tag 089J] is **not** proved here and no declaration in this file carries a Stacks
attribute. What is missing is exactly the induction on the fibre degree: the complement of `U`,
with its reduced induced structure, is again separated and of finite type over `Spec A` and
carries an affine surjective étale chart of strictly smaller fibre degree, and the covers of the
two strata are then assembled by
`AlgebraicGeometry.Space.hasChowSchemeCover_of_isProper_pair`. None of that is done here; the
conjuncts of the conclusion below other than the cover are the inputs that recursion would
consume.

Surjectivity of the morphism produced is **not** claimed, and is false in general.

## References

* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **The cover of the minimal-degree stratum of [Stacks, Tag 089J].**

Let `X` be an algebraic space over `Spec A`, separated and of finite type over the base, with at
least one point, and let `c : h_W ⟶ X` be a surjective étale chart whose underlying scheme is
affine — which exists by Stacks 03H6. Then there are a degree `d` and a nonempty open subset `U`
of the point set of `X`, with `d` positive, such that:

* the base change of the chart along a morphism into `X` is finite locally free of degree `d`
  exactly when the image of that morphism lies in `U`;
* there is an object `X'` of the site, H-quasi-projective over `Spec A`, and a **proper**
  morphism `X' ⟶ X` whose image on points contains `U`;
* the base change of the chart along any morphism into `X` whose image misses `U` entirely is
  finite locally free of degree strictly less than `d`;
* every representable presentation of the fibre of the chart at a field-valued point of `X` is
  finite locally free of some degree at most `d`.

The cover is the construction of [Stacks, Tag 089J] — the complement of the diagonals in
the `d`-fold self-product of the chart over `X`, its scheme-theoretic image in the `d`-fold fibre
power over `Spec A` of a projective compactification of the chart, and the union of the preimages
of the chart in that image — with properness proved by the refined valuative criterion and
H-quasi-projectivity by the projectivity of the compactification. The clauses about the degree
are the degree stratification of Stacks 07S8.

The clauses are what the induction of [Stacks, Tag 089J] on the fibre degree consumes: the
second covers `U`, and the others make the complement of `U` a strictly smaller instance — the
fourth produces the degree of a fibre of the chart inherited by that complement, the third makes
it strictly smaller than `d`, and the first, with positivity of `d`, bounds `d` itself by any
bound already known for the chart. That induction is not performed here. -/
theorem exists_chowCover_minimalDegreeOpen
    (B : BigFppfSite.{u}) (A : CommRingCat.{u}) (hA : B.Contains (Spec A))
    (X : AlgebraicSpaces B (Spec A) hA)
    (hXsep : IsSeparated B (Spec A) hA ((isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj))
    (hft : IsFiniteType B (Spec A) hA ((isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj))
    (Wch : BigFppfOver B (Spec A) hA) (c : yoneda.obj Wch ⟶ X.obj)
    (hc : IsEtale B (Spec A) hA c) (hcs : IsSurjective B (Spec A) hA c)
    (hW : IsAffine ((BigFppfOver.toScheme B (Spec A) hA).obj Wch))
    (hne : Nonempty (points B (Spec A) hA X.obj)) :
    ∃ (d : ℕ) (U : Set (points B (Spec A) hA X.obj)), IsOpen U ∧ U.Nonempty ∧ 0 < d ∧
      (∀ (T : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u) (hm : T ⟶ X.obj),
        IsAlgebraicSpace B (Spec A) hA T →
        ∀ (Pp : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj Wch)
          (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ c hm →
          ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} d)
              (BigFppfOver.toScheme B (Spec A) hA)).presheaf pr₂ ↔
            Set.range (pointsMap B (Spec A) hA T hm) ⊆ U)) ∧
      (∃ (X₁ : BigFppfOver B (Spec A) hA) (p₁ : yoneda.obj X₁ ⟶ X.obj),
        IsProper B (Spec A) hA p₁ ∧
          IsHQuasiProjective (B.inclusion.map X₁.hom) ∧
            U ⊆ Set.range (pointsMap B (Spec A) hA (yoneda.obj X₁) p₁)) ∧
      (∀ (T : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u) (hm : T ⟶ X.obj)
        (Pp : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj Wch)
        (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ c hm → points B (Spec A) hA T →
            Set.range (pointsMap B (Spec A) hA T hm) ⊆ Uᶜ →
              ∀ r : ℕ,
                (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                  (BigFppfOver.toScheme B (Spec A) hA)).presheaf pr₂ → r < d) ∧
      ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B (Spec A) hA)
        (_ : (BigFppfOver.toScheme B (Spec A) hA).obj T ≅ Spec (CommRingCat.of K))
        (ξ : yoneda.obj T ⟶ X.obj) (Vf : BigFppfOver B (Spec A) hA) (q : Vf ⟶ T)
        (i : yoneda.obj Vf ⟶ yoneda.obj Wch),
        IsPullback i (yoneda.map q) c ξ →
          ∃ r : ℕ, r ≤ d ∧
            IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B (Spec A) hA).map q) r := by
  classical
  have hWsep : Scheme.IsSeparated ((BigFppfOver.toScheme B (Spec A) hA).obj Wch) := by
    have := hW
    infer_instance
  have hWc : CompactSpace ((BigFppfOver.toScheme B (Spec A) hA).obj Wch) := by
    have := hW
    infer_instance
  have hsep : IsSeparated B (Spec A) hA c :=
    isSeparated_of_isEtale_of_scheme_isSeparated B (Spec A) hA X.obj X.property Wch hWsep c hc
  have hR : IsReasonableSpace B (Spec A) hA X.obj :=
    isReasonableSpace_of_isSeparated_toBase B (Spec A) hA inferInstance X.obj X.property hXsep
  obtain ⟨d, U, hUopen, hUne, hU1, hU2, hU3⟩ :=
    exists_minimalDegreeOpen_and_fibre_le_degree B (Spec A) hA X.obj Wch c X.property hR hW
      hc hsep hne
  -- the canonical representable base change of the chart
  have hcp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec A) hA)).presheaf c :=
    (isEtale_iff_presheaf_of_yoneda B (Spec A) hA c).1 hc
  -- the degree is positive, because the chart is surjective
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 := by
    obtain ⟨x, hxU⟩ := hUne
    obtain ⟨p, hp⟩ := Quot.exists_rep x
    set ξ : yoneda.obj p.siteObject ⟶ X.obj := yonedaEquiv.symm p.value with hξ
    have hxval : ∀ z, pointsMap B (Spec A) hA (yoneda.obj p.siteObject) ξ z = x := fun z ↦
      (FieldValuedPoint.pointsMap_eq_class B (Spec A) hA p z).trans hp
    have hsq : IsPullback (yoneda.map (hcp.rep.fst' ξ)) (yoneda.map (hcp.rep.snd ξ)) c ξ :=
      hcp.rep.isPullback' ξ
    have hflf := (hU1 (yoneda.obj p.siteObject) ξ
      (isAlgebraicSpace_yoneda B (Spec A) hA p.siteObject)
      (yoneda.obj (hcp.rep.pullback ξ)) (yoneda.map (hcp.rep.fst' ξ))
      (yoneda.map (hcp.rep.snd ξ)) hsq).2 (by
        rintro y ⟨z, rfl⟩
        rw [hxval z]
        exact hxU)
    have hid : IsPullback (𝟙 (yoneda.obj (hcp.rep.pullback ξ)))
        (yoneda.map (hcp.rep.snd ξ)) (yoneda.map (hcp.rep.snd ξ)) (𝟙 (yoneda.obj p.siteObject)) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    have hrank : IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B (Spec A) hA).map (hcp.rep.snd ξ)) d :=
      isFiniteLocallyFreeOfRank_of_presheaf B (Spec A) hA hflf (𝟙 _) (𝟙 _) (hcp.rep.snd ξ) hid
    -- the fibre has a point, because the chart is surjective
    obtain ⟨w, hw⟩ := hcs x
    obtain ⟨z, -, -⟩ := exists_points_of_isPullback B (Spec A) hA hsq w
      (fieldSpecPoint B (Spec A) hA p.contained p.toBase)
      (hw.trans (hxval (fieldSpecPoint B (Spec A) hA p.contained p.toBase)).symm)
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      have hempty : IsEmpty ((BigFppfOver.toScheme B (Spec A) hA).obj (hcp.rep.pullback ξ)) :=
        isEmpty_of_isFiniteLocallyFreeOfRank_zero_of_specTarget
          (K := p.carrier) ((BigFppfOver.toScheme B (Spec A) hA).map (hcp.rep.snd ξ)) hrank
      exact hempty.elim (pointsEquivScheme B (Spec A) hA (hcp.rep.pullback ξ) z)
    · exact ⟨d - 1, by omega⟩
  -- the compactification of the chart, as an object of the site
  obtain ⟨Yo, j, hj, hYo⟩ :=
    exists_compactificationObj_of_isAffine B A hA Wch hW
      (locallyOfFiniteType_hom_of_isEtale B (Spec A) hA X.property Wch c hc hft.1)
  -- the complement of the diagonals, as an object of the site
  obtain ⟨V, ⟨e⟩⟩ :=
    SpacesEtale.exists_siteObj_iso_underlying_diagonalComplement B (Spec A) hA X
      (SpacesEtale.chartObj B (Spec A) hA X Wch c hc)
      (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj Wch))) n hsep
  -- the side conditions
  have hXqc : IsQuasiCompactSpace B (Spec A) hA X.obj :=
    isQuasiCompactSpace_of_isQuasiCompact_toBase B (Spec A) hA
      ((isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj) hft.2
  have hcqc : IsQuasiCompact B (Spec A) hA c :=
    isQuasiCompact_of_compactSpace_source B (Spec A) hA Wch c hWc hXsep
  have hVc : CompactSpace ((BigFppfOver.toScheme B (Spec A) hA).obj V) :=
    SpacesEtale.compactSpace_of_iso_underlying_diagonalComplement B (Spec A) hA X Wch c hc
      hsep (n + 1) V e hXqc hcqc
  have hFPqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B (Spec A) hA).obj
      (overProdObj B (Spec A) hA (fun _ : Fin (n + 1) ↦ Yo))) :=
    quasiSeparatedSpace_of_isSeparated_toSpec _
      (isProper_of_isProjectiveMorphism _
        (isProjectiveMorphism_overProdObj_hom B (Spec A) hA
          (fun _ : Fin (n + 1) ↦ Yo) fun _ ↦ hYo)).toIsSeparated
  have hVqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B (Spec A) hA).map
      (chowToOverProd B (Spec A) hA X Wch c hc hsep Yo j n V e)) :=
    have := hVc
    have := hFPqs
    quasiCompact_of_compactSpace _
  have hqp : IsHQuasiProjective (B.inclusion.map
      (chowCoverObj B (Spec A) hA X Wch c hc hsep Yo j n V e hj).hom) :=
    isHQuasiProjective_chowCoverObj_hom B A hA X Wch c hc hsep Yo j n V e hj hYo hWc
  have hX'qs : QuasiSeparatedSpace ((BigFppfOver.toScheme B (Spec A) hA).obj
      (chowCoverObj B (Spec A) hA X Wch c hc hsep Yo j n V e hj)) :=
    quasiSeparatedSpace_of_isSeparated_toSpec _ hqp.isSeparated
  -- the glued morphism
  obtain ⟨rho, hrho, psi, hpsi, -⟩ :=
    exists_chowCoverHom B (Spec A) hA X Wch c hc hsep Yo j n V e hj
      ((isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj) hXsep hVqc
  -- properness
  obtain ⟨hprop, -⟩ :=
    isProper_and_isHQuasiProjective_chowCoverHom B A hA X Wch c hc hsep Yo j n V e hj hcs hYo
      hWc hXsep hVqc hVc hX'qs
      (exists_eq_of_minimalDegreeOpen B (Spec A) hA Wch c hc (n + 1) hU3)
      rho hrho psi hpsi 0
  exact ⟨n + 1, U, hUopen, hUne, Nat.succ_pos n, hU1,
    ⟨chowCoverObj B (Spec A) hA X Wch c hc hsep Yo j n V e hj, psi, hprop, hqp,
      subset_range_pointsMap_chowCoverHom B (Spec A) hA X Wch c hc hsep Yo j n V e hj U hU1
        rho hrho psi hpsi 0⟩,
    hU2, hU3⟩

end AlgebraicGeometry.Space

end
