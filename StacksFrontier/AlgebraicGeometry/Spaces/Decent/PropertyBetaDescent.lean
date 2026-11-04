module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleOverField

/-!
# Property `(β)` descends along a quasi-compact étale morphism

Stacks 03L2 says that three conditions on an algebraic space — property `(β)` of Stacks 03JX,
decency and reasonableness — pass from the source of a quasi-compact étale morphism which is
surjective on points to its target. This file proves the case of property `(β)`.

## Main results

* `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_surjective_isEtale`:
  **Stacks 03L2** for property `(β)`.

## Implementation notes

The argument is the one of the source. A point `y` of the target has a preimage `x`, and
property `(β)` for the source presents `x` by a monomorphism `Spec k ⟶ X`, by the equivalence
of conditions (1) and (4) of Stacks 03JU. The composite `Spec k ⟶ X ⟶ Y` presents `y`, and by
conditions (1) and (3) of Stacks 03JU it suffices to see that the two projections of its
self-intersection are étale and quasi-compact after every representable base change.

That self-intersection `Spec k ×_Y Spec k` is represented, the target having a representable
diagonal, and its first projection factors as

`Spec k ×_Y Spec k ⟶ Spec k ×_Y X ⟶ Spec k`,

where the first morphism is a monomorphism because `Spec k ⟶ X` is one. The middle term is the
fibre of a quasi-compact étale morphism over a field-valued point, so it is a finite disjoint
union of spectra of finite separable extensions of `k`
(`AlgebraicGeometry.Space.exists_finite_coproduct_spectra_fibre_of_isEtale_isQuasiCompact`),
and Stacks 03DP identifies a monomorphism into such a scheme with the inclusion of a subfamily
of its components. So `Spec k ×_Y Spec k` is itself a finite disjoint union of spectra of
finite separable extensions of `k`; it is therefore quasi-compact, and its projection is étale
by Stacks 03PC. The two projections of a self-intersection are exchanged by the symmetry of the
fibre product, so the one computation serves for both.

Surjectivity of `|X| → |Y|` is surjectivity of the induced map on equivalence classes of
field-valued points, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/RelativeDecency.lean`.

## References

* [Stacks Project, Tag 03DP](https://stacks.math.columbia.edu/tag/03DP)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03L2](https://stacks.math.columbia.edu/tag/03L2)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03L2, property `(β)`.** Let `f : X ⟶ Y` be a quasi-compact étale morphism of
algebraic spaces over `S` which is surjective on points. If `X` has property `(β)` of
Stacks 03JX — every point has a field-valued representative with a finite relation fibre —
then so does `Y`. -/
@[stacks 03L2 "property (beta)"]
theorem hasFiniteRelationFibersAtEveryPoint_of_surjective_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hq : IsQuasiCompact B S hS f)
    (he : IsEtale B S hS f) (hs : Function.Surjective (pointsMap B S hS X f))
    (hβ : HasFiniteRelationFibersAtEveryPoint B S hS X) :
    HasFiniteRelationFibersAtEveryPoint B S hS Y := by
  classical
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  intro y
  obtain ⟨x, hxy⟩ := hs y
  -- a monomorphic field-valued representative of a preimage of `y`
  obtain ⟨p, hpclass, hpmono⟩ :=
    (hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative
        B S hS hX x).mp
      ((hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
          B S hS X hX x).mp
        ((hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS X hX x).mp (hβ x)))
  set pY := FieldValuedPoint.map B S hS X f p with hpYdef
  set gX := fieldMorphism B S hS X p with hgXdef
  set gY := fieldMorphism B S hS Y pY with hgYdef
  have hpYclass : pY.class B S hS Y = y := by
    rw [hpYdef, ← pointsMap_class, hpclass, hxy]
  have hcomp : gY = gX ≫ f := fieldMorphism_map B S hS X f p
  have heV : (BigFppfOver.toScheme B S hS).obj pY.siteObject ≅
      Spec (CommRingCat.of pY.carrier) := Iso.refl _
  -- the fibre of `f` over the field point is a finite disjoint union of spectra of fields
  obtain ⟨U, eF, v, I, hI, K, hKfield, hKalg, hKfin, hKsep, eU, heFfst, heUmap⟩ :=
    exists_finite_coproduct_spectra_fibre_of_isEtale_isQuasiCompact B S hS hX hY f he hq
      pY.carrier pY.siteObject heV gY
  have _ := hI
  let (i : I) : Field (K i) := hKfield i
  let (i : I) : Algebra pY.carrier (K i) := hKalg i
  -- the self-intersection of the field point, which is represented
  have hgrep : yoneda.relativelyRepresentable gY :=
    Functor.relativelyRepresentable.of_diag hY.diagonal_representable gY
  set R : BigFppfOver B S hS := hgrep.pullback gY with hRdef
  set r₁ := hgrep.fst' gY with hr₁def
  set r₂ := hgrep.snd gY with hr₂def
  have hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) gY gY := hgrep.isPullback' gY
  -- it maps monomorphically into the fibre
  have hqw : yoneda.map r₁ ≫ gY = (yoneda.map r₂ ≫ gX) ≫ f :=
    calc yoneda.map r₁ ≫ gY = yoneda.map r₂ ≫ gY := hR.w
      _ = yoneda.map r₂ ≫ gX ≫ f := congrArg (fun z ↦ yoneda.map r₂ ≫ z) hcomp
      _ = (yoneda.map r₂ ≫ gX) ≫ f := (Category.assoc _ _ _).symm
  set qMap : yoneda.obj R ⟶ pullback gY f :=
    pullback.lift (yoneda.map r₁) (yoneda.map r₂ ≫ gX) hqw with hqMapdef
  have hqMapMono : Mono qMap := by
    refine ⟨fun {Z} α β hαβ ↦ ?_⟩
    have h₁ : α ≫ yoneda.map r₁ = β ≫ yoneda.map r₁ := by
      have h := congrArg (fun z ↦ z ≫ pullback.fst gY f) hαβ
      simpa only [hqMapdef, Category.assoc, pullback.lift_fst] using h
    have h₂ : α ≫ yoneda.map r₂ = β ≫ yoneda.map r₂ := by
      have _ : Mono gX := hpmono
      have h := congrArg (fun z ↦ z ≫ pullback.snd gY f) hαβ
      simp only [hqMapdef, Category.assoc, pullback.lift_snd] at h
      exact (cancel_mono gX).1 ((Category.assoc α (yoneda.map r₂) gX).trans
        (h.trans (Category.assoc β (yoneda.map r₂) gX).symm))
    exact hR.hom_ext h₁ h₂
  have _ := hqMapMono
  set mR : R ⟶ U := yoneda.preimage (qMap ≫ eF.hom) with hmRdef
  have hmR : yoneda.map mR = qMap ≫ eF.hom := yoneda.map_preimage _
  have hmRv : mR ≫ v = r₁ := yoneda.map_injective <| by
    rw [Functor.map_comp, hmR, Category.assoc, heFfst, hqMapdef]
    exact pullback.lift_fst _ _ _
  have hmRmono : Mono mR := yoneda.mono_of_mono_map (by rw [hmR]; infer_instance)
  have _ := hmRmono
  have hmRschemeMono : Mono ((BigFppfOver.toScheme B S hS).map mR) :=
    Functor.map_mono (BigFppfOver.toScheme B S hS) mR
  have _ := hmRschemeMono
  obtain ⟨J, eSub, heSub⟩ := AlgebraicGeometry.exists_iso_coproduct_spec_of_mono K
    ((BigFppfOver.toScheme B S hS).map mR ≫ eU.hom)
  -- so the first projection of the self-intersection is étale, and its source is quasi-compact
  have hprojFactor : eSub.hom ≫ Sigma.desc (fun j : J ↦
      Spec.map (CommRingCat.ofHom (algebraMap pY.carrier (K j.1)))) =
      (BigFppfOver.toScheme B S hS).map r₁ ≫ heV.hom := by
    have hdesc : Sigma.desc (fun j : J ↦ Sigma.ι
          (fun i : I ↦ Spec (CommRingCat.of (K i))) j.1) ≫
        Sigma.desc (fun i : I ↦ Spec.map
          (CommRingCat.ofHom (algebraMap pY.carrier (K i)))) =
        Sigma.desc (fun j : J ↦ Spec.map
          (CommRingCat.ofHom (algebraMap pY.carrier (K j.1)))) :=
      Sigma.hom_ext _ _ fun j ↦ by simp
    rw [← hdesc, ← Category.assoc, heSub, Category.assoc, heUmap, ← Category.assoc,
      ← Functor.map_comp, hmRv]
  have hr₁Et : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r₁) :=
    (MorphismProperty.cancel_right_of_respectsIso
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) _ heV.hom).1
      ((AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable pY.carrier
          ((BigFppfOver.toScheme B S hS).map r₁ ≫ heV.hom)).2
        ⟨J, (fun j : J ↦ K j.1), (fun j ↦ hKfield j.1), (fun j ↦ hKalg j.1),
          (fun j ↦ hKfin j.1), (fun j ↦ hKsep j.1), eSub, hprojFactor⟩)
  have hRcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj R) := by
    have _ : CompactSpace ↥(∐ fun j : J ↦ Spec (CommRingCat.of (K j.1))) :=
      (AlgebraicGeometry.sigmaMk fun j : J ↦ Spec (CommRingCat.of (K j.1))).compactSpace
    exact (Scheme.homeoOfIso eSub.symm).compactSpace
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj pY.siteObject) :=
    IsAffine.of_isIso heV.hom
  have _ := hVaff
  have hr₁QC : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map r₁) :=
    quasiCompact_of_compactSpace_of_isAffine _ inferInstance hRcpt
  -- both projections therefore have the property asked of a field-valued representative
  set Qscheme : MorphismProperty Scheme.{u} :=
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) with hQscheme
  set Qsite : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage Qscheme (BigFppfOver.toScheme B S hS) with hQsite
  have _ : MorphismProperty.IsStableUnderBaseChange Qscheme := by
    rw [hQscheme]
    exact MorphismProperty.IsStableUnderBaseChange.inf
  have _ : MorphismProperty.RespectsIso Qscheme :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : Qsite.IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange (BigFppfOver.toScheme B S hS) Qscheme
  have _ : Qsite.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have _ : Qsite.presheaf.RespectsIso := inferInstance
  have hpreFst : Qsite.presheaf (pullback.fst gY gY) :=
    (Qsite.presheaf.cancel_left_of_respectsIso hR.isoPullback.hom _).mp (by
      rw [hR.isoPullback_hom_fst]
      exact MorphismProperty.relative_map (F := yoneda) ⟨hr₁Et, hr₁QC⟩)
  have hpreSnd : Qsite.presheaf (pullback.snd gY gY) := by
    have hfac : Qsite.presheaf ((pullbackSymmetry gY gY).hom ≫ pullback.fst gY gY) :=
      (Qsite.presheaf.cancel_left_of_respectsIso (pullbackSymmetry gY gY).hom _).mpr hpreFst
    simpa only [pullbackSymmetry_hom_comp_fst] using hfac
  exact (hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS Y hY y).mpr
    ((hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
      B S hS Y hY y).mpr ⟨pY, hpYclass, hpreFst, hpreSnd⟩)

end AlgebraicGeometry.Space

end
