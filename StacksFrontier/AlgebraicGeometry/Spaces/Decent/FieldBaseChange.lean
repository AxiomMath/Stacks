module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFromQuasiCompactRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
import StacksCore.Tactic.StacksAttribute

/-!
# Decency of an algebraic space under restriction to a smaller affine base

Let `g : S' ⟶ S` be a morphism of affine schemes in a big fppf site and let `X` be an
algebraic space over `S`. Restriction along `g` turns `X` into an algebraic space over `S'`,
and this file shows that decency is inherited: every point of the restriction is presented by
a quasi-compact monomorphism from the spectrum of a field.

The input needed for the argument is the implication (5) `⟹` (4) of Stacks 03JV, which is
also proved here: a point presented by *some* quasi-compact morphism from a field spectrum is
presented by one which is moreover a monomorphism.

## Main results

* `hasQuasiCompactMonomorphicFieldRepresentative_of_hasQuasiCompactFieldRepresentative` is
  **Stacks 03JV, condition (5) implies condition (4)**.
* `AlgebraicGeometry.Space.isDecentSpace_relocalizeRestrict`: decency of an algebraic space
  over an affine base is preserved by restriction along a morphism of affine bases.

## Implementation notes

For (5) `⟹` (4) the route is through condition (1), finiteness of the fibres of every affine
étale chart and of its self-intersection: the monomorphism condition of condition (3) is not
available from condition (5), whereas condition (1) needs no monomorphism at all. The base
change of an affine étale chart along a quasi-compact field-valued point is a quasi-compact
scheme étale over a one-point scheme, hence finite, and the self-intersection of that base
change is finite for the same reason; both fibres are then images of finite sets. Condition
(1) is turned back into condition (4) by
`hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative`.

The restriction statement is proved by producing, from a field-valued point of the restricted
space, the field-valued point of `X` with the same field obtained by composing its structure
morphism with `g`. The presenting morphism of the restricted point factors as the tautological
comparison morphism `h_{Spec k} ⟶ (h_{Spec k})|_{S'}` followed by the restriction of the
presenting morphism over `S`. The first factor is, by
`CategoryTheory.OverShriek.restrictYonedaUnit_eq`, the Yoneda image of a morphism of the site
with affine source and target — this is where affineness of `S` and `S'` is used — and the
second is quasi-compact by
`CategoryTheory.OverShriek.relative_relocalizeRestrict_map`.

## References

* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section FixedBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (5) of Stacks 03JV implies condition (1) -/

/-- A fibre of `|Y| → |X|` above the point presented by a field-valued point `p` is finite as
soon as the projection `Y ×_X Spec k ⟶ Y` factors through a representable presheaf with
finitely many points. -/
private theorem finite_fibre_of_factor_pullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS X) (γ : Y ⟶ X)
    {W : BigFppfOver B S hS} [Finite ((BigFppfOver.toScheme B S hS).obj W)]
    (a : yoneda.obj W ⟶ Y)
    (l : pullback γ (fieldMorphism B S hS X p) ⟶ yoneda.obj W)
    (hl : l ≫ a = pullback.fst γ (fieldMorphism B S hS X p)) :
    (pointsMap B S hS Y γ ⁻¹' {p.class B S hS X}).Finite := by
  have _ : Finite (points B S hS (yoneda.obj W)) :=
    Finite.of_equiv _ (pointsEquivScheme B S hS W).symm
  refine Set.Finite.subset (Set.finite_range (pointsMap B S hS (yoneda.obj W) a)) ?_
  intro y hy
  obtain ⟨z, hz⟩ : y ∈ Set.range (pointsMap B S hS
      (pullback γ (fieldMorphism B S hS X p))
      (pullback.fst γ (fieldMorphism B S hS X p))) := by
    rw [range_pointsMap_fibre_fieldMorphism B S hS γ p]
    exact hy
  exact ⟨pointsMap B S hS _ l z, by rwa [← pointsMap_comp_apply, hl]⟩

/-- **Stacks 03JV, condition (5) implies condition (1).** A point of an algebraic space
presented by a quasi-compact morphism from the spectrum of a field has finite fibres on every
affine étale chart and on the self-intersection of every such chart. -/
private theorem hasFiniteChartAndRelationFibersAt_of_isQuasiCompact_fieldMorphism
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B S hS X)
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS X p)) :
    HasFiniteChartAndRelationFibersAt B S hS X (p.class B S hS X) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  intro U hU φ hφ
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  refine ⟨finite_fibre_pointsMap_of_isQuasiCompact_fieldMorphism B S hS p hqc hcpt φ hφ, ?_⟩
  set f := fieldMorphism B S hS X p
  set q := hφ.rep.snd f
  have hs : IsPullback (yoneda.map (hφ.rep.fst' f)) (yoneda.map q) φ f := hφ.rep.isPullback' f
  have _ : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj (hφ.rep.pullback f)) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      ((hqc (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (isQuasiCompactSpace_yoneda_obj B S hS hcpt) φ).of_iso B S hS
          ((IsPullback.of_hasPullback φ f).isoIsPullback _ _ (hφ.rep.isPullback f)))
  have _ : Etale ((BigFppfOver.toScheme B S hS).map q) := hφ.property_snd f
  have _ : Finite ((BigFppfOver.toScheme B S hS).obj (hφ.rep.pullback f)) :=
    finite_of_etale_of_subsingleton ((BigFppfOver.toScheme B S hS).map q)
  -- the self-intersection of the base-changed chart is again finite over the field
  have hqqS := (IsPullback.of_hasPullback q q).map (BigFppfOver.toScheme B S hS)
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map q) :=
    quasiCompact_of_compactSpace_of_isAffine _ inferInstance inferInstance
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map (pullback.fst q q)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hqqS.flip inferInstance
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst q q)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hqqS.flip inferInstance
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj (pullback q q)) :=
    QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map (pullback.fst q q))
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst q q ≫ q)) := by
    rw [Functor.map_comp]
    infer_instance
  have _ : Finite ((BigFppfOver.toScheme B S hS).obj (pullback q q)) :=
    finite_of_etale_of_subsingleton ((BigFppfOver.toScheme B S hS).map (pullback.fst q q ≫ q))
  -- the relation fibre is the image of the finite self-intersection
  have hqq := (IsPullback.of_hasPullback q q).map yoneda
  have hb : (yoneda.map (pullback.fst q q) ≫ yoneda.map (hφ.rep.fst' f)) ≫ φ =
      (yoneda.map (pullback.snd q q) ≫ yoneda.map (hφ.rep.fst' f)) ≫ φ := by
    simp only [Category.assoc, hs.w]
    simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ f) hqq.w
  have h₁ : (pullback.fst (pullback.fst φ φ ≫ φ) f ≫ pullback.fst φ φ) ≫ φ =
      pullback.snd (pullback.fst φ φ ≫ φ) f ≫ f := by
    simpa only [Category.assoc] using
      pullback.condition (f := pullback.fst φ φ ≫ φ) (g := f)
  have h₂ : (pullback.fst (pullback.fst φ φ ≫ φ) f ≫ pullback.snd φ φ) ≫ φ =
      pullback.snd (pullback.fst φ φ ≫ φ) f ≫ f := by
    rwa [Category.assoc, ← pullback.condition (f := φ) (g := φ), ← Category.assoc]
  have hl : hqq.lift (hs.lift (pullback.fst (pullback.fst φ φ ≫ φ) f ≫ pullback.fst φ φ)
        (pullback.snd (pullback.fst φ φ ≫ φ) f) h₁)
      (hs.lift (pullback.fst (pullback.fst φ φ ≫ φ) f ≫ pullback.snd φ φ)
        (pullback.snd (pullback.fst φ φ ≫ φ) f) h₂) (by simp) ≫
      pullback.lift (yoneda.map (pullback.fst q q) ≫ yoneda.map (hφ.rep.fst' f))
        (yoneda.map (pullback.snd q q) ≫ yoneda.map (hφ.rep.fst' f)) hb =
      pullback.fst (pullback.fst φ φ ≫ φ) f := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hqq.lift_fst, hs.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hqq.lift_snd, hs.lift_fst]
  exact finite_fibre_of_factor_pullback B S hS p (pullback.fst φ φ ≫ φ) _ _ hl

/-- **Stacks 03JV, condition (5) implies condition (4).** If some field-valued point in the
class of `x` presents it by a quasi-compact morphism, then some field-valued point in that
class presents it by a morphism which is both a monomorphism and quasi-compact. -/
@[stacks 03JV "condition (5) implies condition (4)"]
theorem hasQuasiCompactMonomorphicFieldRepresentative_of_hasQuasiCompactFieldRepresentative
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasQuasiCompactFieldRepresentative B S hS F x) :
    HasQuasiCompactMonomorphicFieldRepresentative B S hS F x := by
  obtain ⟨p, rfl, hqc⟩ := h
  exact (hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative
    B S hS F hF _).mp
      (hasFiniteChartAndRelationFibersAt_of_isQuasiCompact_fieldMorphism B S hS F p hqc)

end FixedBase

/-! ### Restriction to a smaller affine base -/

/-- **Restriction preserves quasi-compactness of a relatively representable morphism.** The
two readings of quasi-compactness agree for such a morphism (Stacks 03HD), and the reading by
represented base changes is inherited by reindexing. -/
private theorem isQuasiCompact_relocalizeRestrict_map (B : BigFppfSite.{u})
    (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS' ⟶ B.obj hS) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hrep : yoneda.relativelyRepresentable f) (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S' hS' ((OverShriek.relocalizeRestrict g).map f) := by
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact isQuasiCompact_of_presheaf_quasiCompact B S' hS'
    (OverShriek.relative_relocalizeRestrict_map g
      (inverseImage_restrictReindexSnd B S' S hS' hS g
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
      (presheaf_quasiCompact_of_isQuasiCompact B S hS hrep hf))

/-- Decency of an algebraic space over an affine scheme `S` is preserved by restriction along a
morphism `g : S' ⟶ S` of affine schemes of the site: every point of the restricted space is
presented by a quasi-compact monomorphism from the spectrum of a field. -/
@[stacks 0ABT "decency under change of affine base"]
theorem isDecentSpace_relocalizeRestrict (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    [IsAffine S] [IsAffine S']
    (g : B.obj hS' ⟶ B.obj hS)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hdecent : IsDecentSpace B S hS X) :
    IsDecentSpace B S' hS' ((CategoryTheory.OverShriek.relocalizeRestrict g).obj X) := by
  have hXK := isAlgebraicSpace_relocalizeRestrict B S' S hS' hS g X hX
  have _ : IsAffine (B.inclusion.obj (B.obj hS)) := ‹IsAffine S›
  have _ : IsAffine (B.inclusion.obj (B.obj hS')) := ‹IsAffine S'›
  set XK := (CategoryTheory.OverShriek.relocalizeRestrict g).obj X
  intro x
  obtain ⟨pK, rfl⟩ := Quot.exists_rep x
  refine hasQuasiCompactMonomorphicFieldRepresentative_of_hasQuasiCompactFieldRepresentative
    B S' hS' _ hXK ⟨pK, rfl, ?_⟩
  set AK := pK.siteObject B S' hS' XK
  set t := fieldMorphism B S' hS' XK pK
  -- the field-valued point of `X` presented by the restriction of the section of `pK`
  let p : FieldValuedPoint B S hS X :=
    { carrier := pK.carrier
      contained := pK.contained
      toBase := pK.toBase ≫ B.inclusion.map g
      value := yonedaEquiv (OverShriek.restrictYonedaEquiv g AK X t) }
  have hfm : fieldMorphism B S hS X p = OverShriek.restrictYonedaEquiv g AK X t :=
    yonedaEquiv.symm_apply_apply _
  -- the tautological comparison morphism out of the field spectrum over `S'`
  let u : AK ⟶ (Over.pullback g).obj ((Over.map g).obj AK) :=
    (Over.mapPullbackAdj g).unit.app AK
  let d : yoneda.obj AK ⟶ (OverShriek.relocalizeRestrict g).obj (yoneda.obj p.siteObject) :=
    (OverShriek.restrictYonedaEquiv g AK (yoneda.obj ((Over.map g).obj AK))).symm
      (𝟙 (yoneda.obj ((Over.map g).obj AK)))
  have hunit : d = yoneda.map u ≫
      (OverShriek.restrictYonedaIso g ((Over.map g).obj AK)).hom :=
    OverShriek.restrictYonedaUnit_eq g AK
  -- both ends of that morphism are affine, so it is quasi-compact
  have hsrc : IsAffine ((BigFppfOver.toScheme B S' hS').obj AK) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of pK.carrier)))
  have _ : IsAffine (B.inclusion.obj ((Over.map g).obj AK).left) := hsrc
  have _ : AlgebraicGeometry.IsAffineHom
      (B.inclusion.map ((Over.map g).obj AK).hom) := inferInstance
  have hpbA := (IsPullback.of_hasPullback ((Over.map g).obj AK).hom g).map B.inclusion
  have h0 : IsAffine (pullback (B.inclusion.map ((Over.map g).obj AK).hom)
    (B.inclusion.map g)) := inferInstance
  have _ : IsAffine ((BigFppfOver.toScheme B S' hS').obj
      ((Over.pullback g).obj ((Over.map g).obj AK))) :=
    @IsAffine.of_isIso _ _ hpbA.isoPullback.hom _ h0
  have hu : IsQuasiCompact B S' hS' (yoneda.map u) :=
    isQuasiCompact_yoneda_map_of_isAffineHom B S' hS' u inferInstance
  have hd : IsQuasiCompact B S' hS' d := by
    refine isQuasiCompact_of_presheaf_quasiCompact B S' hS' ?_
    rw [hunit]
    exact MorphismProperty.RespectsIso.postcomp _ _ _
      (presheaf_quasiCompact_of_isQuasiCompact B S' hS'
        (Functor.relativelyRepresentable.map yoneda _) hu)
  -- the restriction of the presenting morphism over `S` is quasi-compact
  have hp : IsQuasiCompact B S hS (fieldMorphism B S hS X p) :=
    (hasQuasiCompactFieldRepresentative_iff_everyFieldRepresentativeIsQuasiCompact
      B S hS X hX).mp
        ((hdecent (p.class B S hS X)).hasQuasiCompactFieldRepresentative B S hS X) p rfl
  have hrest : IsQuasiCompact B S' hS'
      ((OverShriek.relocalizeRestrict g).map (fieldMorphism B S hS X p)) :=
    isQuasiCompact_relocalizeRestrict_map B S S' hS hS' g
      (Functor.relativelyRepresentable.of_diag hX.diagonal_representable _) hp
  have hcomp := isQuasiCompact_comp B S' hS'
    (isAlgebraicSpace_relocalizeRestrict B S' S hS' hS g (yoneda.obj p.siteObject)
      (isAlgebraicSpace_yoneda B S hS p.siteObject)) hXK d _ hd hrest
  have heq : d ≫ (OverShriek.relocalizeRestrict g).map (fieldMorphism B S hS X p) = t := by
    rw [hfm]
    exact (OverShriek.eq_restrictYonedaUnit_comp g t).symm
  rwa [heq] at hcomp

end AlgebraicGeometry.Space

end
