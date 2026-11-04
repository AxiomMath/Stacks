module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RestrictionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAtlas02WRb

/-!
# Restricting a relation of algebraic spaces to a scheme chart

Let `Z` be a presheaf on the big fppf site of a scheme `S`, let `j : R ⟶ U ×_Z U` be a
pre-relation of presheaves over `Z` whose target and source maps are representable and étale,
and let `a : h_{U₀} ⟶ U` be a morphism from a representable presheaf. Then the restriction of
`j` along `a` is again *representable*: there are an object `R₀` of the site and two étale
morphisms `t₀, s₀ : R₀ ⟶ U₀` such that `h_{R₀}` is the restricted relation `R|_{U₀}`, with
`t₀` and `s₀` its target and source.

## Main definitions

* `AlgebraicGeometry.Space.chartInSlice` and `AlgebraicGeometry.Space.chartInSliceMap`: a
  morphism from a representable presheaf to `U`, read as an object of the slice over `Z` and a
  morphism of that slice.

## Main results

* `AlgebraicGeometry.Space.exists_etaleSiteRelation_of_chart`: the restriction of a
  representable étale pre-relation along a chart is represented by an object of the site, with
  étale target and source.
* `AlgebraicGeometry.Space.isIso_restrictQuotientSheafMap_chartInSliceMap`: the quotient sheaf
  of the restriction along a surjective étale chart is the quotient sheaf of the original
  relation.
* `AlgebraicGeometry.Space.exists_etaleSiteRelation_of_isAlgebraicSpace`: the two statements
  together, for an étale atlas of an algebraic space.

## Implementation notes

The restricted relation is again an equivalence relation by the instance
`AlgebraicGeometry.Space.PreRelation.isEquivalenceRelation_restrict` and monic by
`CategoryTheory.Limits.pullback.fst_of_mono`, so neither is restated here.

Nothing here is tagged: this is a step in the proof of the quotient theorem for a relation of
algebraic spaces, and not an assertion of Stacks 02WW.

## References

* [Stacks Project, Tag 043D](https://stacks.math.columbia.edu/tag/043D)
* [Stacks Project, Tag 046P](https://stacks.math.columbia.edu/tag/046P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}

/-- A morphism `a : h_{U₀} ⟶ U` from the presheaf represented by an object of the site, read as
an object of the slice over `Z` by composing with the structure map of `U`. -/
abbrev chartInSlice (U : Over Z) {U₀ : BigFppfOver B S hS} (a : yoneda.obj U₀ ⟶ U.left) :
    Over Z :=
  Over.mk (a ≫ U.hom)

/-- A morphism `a : h_{U₀} ⟶ U` from the presheaf represented by an object of the site, read as
a morphism of the slice over `Z`. -/
abbrev chartInSliceMap (U : Over Z) {U₀ : BigFppfOver B S hS} (a : yoneda.obj U₀ ⟶ U.left) :
    chartInSlice U a ⟶ U :=
  Over.homMk a rfl

/-- The restriction of a pre-relation with representable étale target and source maps along a
morphism from a representable presheaf is represented by an object of the site, with étale
target and source maps. -/
theorem exists_etaleSiteRelation_of_chart (j : PreRelation R U)
    {U₀ : BigFppfOver B S hS} (a : yoneda.obj U₀ ⟶ U.left)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (ht : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.target.left)
    (hs : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.source.left) :
    ∃ (R₀ : BigFppfOver B S hS) (t₀ s₀ : R₀ ⟶ U₀)
      (e : (PreRelation.restriction j (chartInSliceMap U a)).left ≅ yoneda.obj R₀),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) t₀ ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) s₀ ∧
        (PreRelation.restrict j (chartInSliceMap U a)).target.left =
          e.hom ≫ yoneda.map t₀ ∧
        (PreRelation.restrict j (chartInSliceMap U a)).source.left =
          e.hom ≫ yoneda.map s₀ := by
  have hEtaleComp : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hSiteComp : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have hRt : j.target.left ≫ U.hom = R.hom := Over.w j.target
  have hRs : j.source.left ≫ U.hom = R.hom := Over.w j.source
  obtain ⟨P₀, π, p, hP⟩ := ht.1 a
  obtain ⟨Q₀, κ, q, hQ⟩ := hs.1 a
  have hπ := ht.2 a p π hP
  have hκ := hs.2 a q κ hQ
  have hpr := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hP.flip ha
  have hqr := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hQ.flip ha
  obtain ⟨R₀, ρ, w, hR⟩ := hpr.1 q
  obtain ⟨σ, rfl⟩ := yoneda.map_surjective w
  have hρ := hpr.2 q _ ρ hR
  have hσ := hqr.2 p _ σ hR.flip
  let g : chartInSlice U a ⟶ U := chartInSliceMap U a
  let AO : Over Z := Over.mk (yoneda.map π ≫ a ≫ U.hom)
  let a₁ : AO ⟶ chartInSlice U a := Over.homMk (yoneda.map π) rfl
  let a₂ : AO ⟶ R := Over.homMk p (by
    change p ≫ R.hom = yoneda.map π ≫ a ≫ U.hom
    rw [← hRt, ← Category.assoc, hP.w, Category.assoc])
  let DO : Over Z := Over.mk (yoneda.map κ ≫ a ≫ U.hom)
  let d₂ : DO ⟶ chartInSlice U a := Over.homMk (yoneda.map κ) rfl
  let d₁ : DO ⟶ R := Over.homMk q (by
    change q ≫ R.hom = yoneda.map κ ≫ a ≫ U.hom
    rw [← hRs, ← Category.assoc, hQ.w, Category.assoc])
  let PO : Over Z := Over.mk (yoneda.map σ ≫ yoneda.map π ≫ a ≫ U.hom)
  let p₁ : PO ⟶ AO := Over.homMk (yoneda.map σ) rfl
  have hκa : yoneda.map κ ≫ a ≫ U.hom = q ≫ R.hom := by
    rw [← Category.assoc, ← hQ.w, Category.assoc, hRs]
  have hπa : yoneda.map π ≫ a ≫ U.hom = p ≫ R.hom := by
    rw [← Category.assoc, ← hP.w, Category.assoc, hRt]
  let p₂ : PO ⟶ DO := Over.homMk (yoneda.map ρ) (by
    change yoneda.map ρ ≫ yoneda.map κ ≫ a ≫ U.hom =
      yoneda.map σ ≫ yoneda.map π ≫ a ≫ U.hom
    rw [hκa, hπa, ← Category.assoc, ← Category.assoc, ← hR.w])
  have ha' : IsPullback a₁ a₂ g j.target :=
    IsPullback.of_map_of_faithful (Over.forget Z) hP.flip
  have hd' : IsPullback d₁ d₂ j.source g :=
    IsPullback.of_map_of_faithful (Over.forget Z) hQ
  have hp' : IsPullback p₁ p₂ a₂ d₁ :=
    IsPullback.of_map_of_faithful (Over.forget Z) hR
  have hfin : IsPullback (prod.lift (p₁ ≫ a₁) (p₂ ≫ d₂)) (p₁ ≫ a₂) (prod.map g g) j := by
    have h := isPullback_prodLift_of_isPullback ha' hd' hp'
    have hj : (prod.lift j.target j.source : R ⟶ U ⨯ U) = j :=
      prod.hom_ext (by simp) (by simp)
    rwa [hj] at h
  let iso := hfin.isoIsPullback _ _ (IsPullback.of_hasPullback (prod.map g g) j)
  have hfst : iso.hom ≫ PreRelation.restrict j g = prod.lift (p₁ ≫ a₁) (p₂ ≫ d₂) :=
    IsPullback.isoIsPullback_hom_fst _ _ hfin (IsPullback.of_hasPullback _ _)
  have key : ∀ (x : PreRelation.restriction j g ⟶ chartInSlice U a) (y : PO ⟶ chartInSlice U a),
      iso.hom ≫ x = y → x.left = iso.inv.left ≫ y.left := by
    rintro x y rfl
    rw [Over.comp_left, ← Category.assoc, ← Over.comp_left, iso.inv_hom_id, Over.id_left,
      Category.id_comp]
  refine ⟨R₀, σ ≫ π, ρ ≫ κ, ((Over.forget Z).mapIso iso).symm,
    MorphismProperty.comp_mem _ _ _ hσ hπ, MorphismProperty.comp_mem _ _ _ hρ hκ, ?_, ?_⟩
  · simpa [p₁, a₁, Functor.map_comp] using key (PreRelation.restrict j g).target (p₁ ≫ a₁)
      (by rw [PreRelation.target, ← Category.assoc, hfst, prod.lift_fst])
  · simpa [p₂, d₂, Functor.map_comp] using key (PreRelation.restrict j g).source (p₂ ≫ d₂)
      (by rw [PreRelation.source, ← Category.assoc, hfst, prod.lift_snd])

/-- The quotient sheaf of the restriction of a pre-equivalence relation along a surjective étale
chart is the quotient sheaf of the relation itself. -/
theorem isIso_restrictQuotientSheafMap_chartInSliceMap
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (j : PreRelation R U) (hj : IsPreEquivalenceRelation j)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS) U.left)
    {U₀ : BigFppfOver B S hS} (a : yoneda.obj U₀ ⟶ U.left)
    (hasurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsIso (restrictQuotientSheafMap j (chartInSliceMap U a)) :=
  restrictQuotientSheafMap_isIso j (chartInSliceMap U a) hj
    (isLocallySurjective_of_presheaf_surjective_etale B S hS (G := ⟨U.left, hU⟩) hasurj haet)
    hU (isAlgebraicSpace_yoneda B S hS U₀).isSheaf

/-- An equivalence relation of algebraic spaces whose target and source maps are representable
and étale restricts, along an étale atlas of its object space, to a relation between objects of
the big fppf site with étale target and source and with the same quotient sheaf. -/
theorem exists_etaleSiteRelation_of_isAlgebraicSpace
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (j : PreRelation R U) (hj : IsPreEquivalenceRelation j)
    (hU : IsAlgebraicSpace B S hS U.left)
    (ht : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.target.left)
    (hs : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.source.left) :
    ∃ (U₀ R₀ : BigFppfOver B S hS) (a : yoneda.obj U₀ ⟶ U.left) (t₀ s₀ : R₀ ⟶ U₀)
      (e : (PreRelation.restriction j (chartInSliceMap U a)).left ≅ yoneda.obj R₀),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) t₀ ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) s₀ ∧
        (PreRelation.restrict j (chartInSliceMap U a)).target.left =
          e.hom ≫ yoneda.map t₀ ∧
        (PreRelation.restrict j (chartInSliceMap U a)).source.left =
          e.hom ≫ yoneda.map s₀ ∧
        IsIso (restrictQuotientSheafMap j (chartInSliceMap U a)) := by
  obtain ⟨U₀, a, hasurj, haet⟩ := hU.exists_atlas
  obtain ⟨R₀, t₀, s₀, e, ht₀, hs₀, hetgt, hesrc⟩ :=
    exists_etaleSiteRelation_of_chart j a haet ht hs
  exact ⟨U₀, R₀, a, t₀, s₀, e, ht₀, hs₀, hetgt, hesrc,
    isIso_restrictQuotientSheafMap_chartInSliceMap j hj hU.isSheaf a hasurj haet⟩

end AlgebraicGeometry.Space

end
