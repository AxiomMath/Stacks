module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RepresentablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibreFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibreTransfer

/-!
# Finiteness above a point on one étale chart

Let `x` be a point of an algebraic space `F` over a scheme `S`, let `φ : h_U ⟶ F` be an étale
chart and let `R = h_U ×_F h_U`. Stacks 040U states that the following are equivalent:

1. `x` is in the image of `|U| → |F|` and the fibres of `|U| → |F|` and of `|R| → |F|` above `x`
   are both finite;
2. there is a monomorphism `Spec(k) ⟶ F` with `k` a field in the class of `x` for which
   `Spec(k) ×_F U` is a finite nonempty scheme over `k`.

## Main results

* `AlgebraicGeometry.Space.finite_points_fieldFibre_of_isFinite`: a field fibre finite over the
  field in the sense of Stacks 03ZP has finitely many points.
* `AlgebraicGeometry.Space.presheaf_isFinite_pullback_fst_fieldMorphism_of_finite_points`: on an
  étale chart, a field fibre with finitely many points is finite over the field.
* `AlgebraicGeometry.Space.finite_relationFibre_of_finite_chartFibre`: on an étale chart, a
  finite chart fibre and a monomorphic field-valued representative force a finite relation
  fibre.
* `AlgebraicGeometry.Space.finite_chartFibre_and_relationFibre_of_mono_isFinite`: the finiteness
  half of part (1), with no nonemptiness assumed.
* `AlgebraicGeometry.Space.finiteFibres_of_mono_isFinite_fieldFibre`: part (2) implies
  part (1).
* `AlgebraicGeometry.Space.exists_mono_isFinite_fieldFibre_of_finiteFibres`: part (1) implies
  part (2).
* `AlgebraicGeometry.Space.finiteFibres_iff_exists_mono_isFinite_fieldFibre`: the equivalence.
* `AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_everyEtaleChart_of_isDecentSpace`
  and `AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_everyEtaleChart_yoneda`:
  condition (2) of Stacks 03JU implies condition (4) on a decent algebraic space and on a
  represented presheaf.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 040U](https://stacks.math.columbia.edu/tag/040U)
* [Stacks Project, Tag 0AC7](https://stacks.math.columbia.edu/tag/0AC7)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Passing between finiteness of the field fibre and finiteness of its point set -/

/-- If the projection `Spec(k) ×_F U ⟶ Spec(k)` is a finite morphism of algebraic spaces in the
sense of Stacks 03ZP, then the field fibre has finitely many points. -/
theorem finite_points_fieldFibre_of_isFinite {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F) {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ F)
    (hfin : IsFinite B S hS (pullback.fst (fieldMorphism B S hS F p) φ)) :
    Finite (points B S hS (fieldFibre B S hS φ p)) := by
  have hpaff : IsAffine ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  obtain ⟨V, pr, i, hVaff, hprfin, hsq⟩ := hfin p.siteObject hpaff (𝟙 _)
  have : IsIso i := hsq.isIso_fst_of_isIso
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hVfin : Finite ((BigFppfOver.toScheme B S hS).obj V) := by
    rcases isEmpty_or_nonempty ((BigFppfOver.toScheme B S hS).obj V) with _ | hne
    · exact Finite.of_subsingleton
    · obtain ⟨v₀⟩ := hne
      have h := ((BigFppfOver.toScheme B S hS).map pr).finite_preimage_singleton
        ((BigFppfOver.toScheme B S hS).map pr v₀)
      have he : ((BigFppfOver.toScheme B S hS).map pr) ⁻¹'
          {((BigFppfOver.toScheme B S hS).map pr v₀)} = Set.univ :=
        Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
      exact Set.finite_univ_iff.mp (he ▸ h)
  have hVpts : Finite (points B S hS (yoneda.obj V)) :=
    Finite.of_equiv _ (pointsEquivScheme B S hS V).symm
  exact Finite.of_surjective _ (bijective_pointsMap_of_isIso B S hS
    (i ≫ (pullbackSymmetry (fieldMorphism B S hS F p) φ).hom)).2

/-- For an étale chart `φ : h_U ⟶ F` and a field-valued point `p` of `F` whose field fibre has a
finite point set, the projection `Spec(k) ×_F U ⟶ Spec(k)` is relatively representable with every
represented base change a finite morphism of schemes. -/
theorem presheaf_isFinite_pullback_fst_fieldMorphism_of_finite_points
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F)
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ F} (hφ : IsEtale B S hS φ)
    (hfin : Finite (points B S hS (fieldFibre B S hS φ p))) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.fst (fieldMorphism B S hS F p) φ) := by
  have hφp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ := presheaf_etale_of_isEtale B S hS hφ
  have sqW := hφp.rep.isPullback (fieldMorphism B S hS F p)
  have hWet : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (hφp.rep.snd (fieldMorphism B S hS F p))) := hφp.property_snd _
  have hpts : Finite (points B S hS (yoneda.obj
      (hφp.rep.pullback (fieldMorphism B S hS F p)))) :=
    Finite.of_surjective _ (bijective_pointsMap_of_isIso B S hS
      ((IsPullback.of_hasPullback φ (fieldMorphism B S hS F p)).isoIsPullback _ _ sqW).hom).2
  have hsch : Finite ((BigFppfOver.toScheme B S hS).obj
      (hφp.rep.pullback (fieldMorphism B S hS F p))) :=
    Finite.of_equiv _ (pointsEquivScheme B S hS _)
  have hmap : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      (hφp.rep.snd (fieldMorphism B S hS F p))) :=
    isFinite_of_etale_of_finite p.carrier ((BigFppfOver.toScheme B S hS).map
      (hφp.rep.snd (fieldMorphism B S hS F p)))
  set Q := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hQbc : Q.IsStableUnderBaseChange := by
    constructor
    intro W Y Z T f g f' g' sq hg
    show _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g')
    change _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g) at hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (CategoryTheory.IsPullback.map (BigFppfOver.toScheme B S hS) sq) hg
  have hQpre : Q.presheaf (yoneda.map (hφp.rep.snd (fieldMorphism B S hS F p))) :=
    MorphismProperty.relative_map hmap
  have hRI : (Q.presheaf).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange Q (F := yoneda)).respectsIso
  have harrow : Arrow.mk (pullback.fst (fieldMorphism B S hS F p) φ) ≅
      Arrow.mk (yoneda.map (hφp.rep.snd (fieldMorphism B S hS F p))) :=
    Arrow.isoMk ((IsPullback.of_hasPullback (fieldMorphism B S hS F p) φ).isoIsPullback
      _ _ sqW.flip) (Iso.refl _)
      (((IsPullback.of_hasPullback (fieldMorphism B S hS F p) φ).isoIsPullback_hom_fst
        _ _ sqW.flip).trans
        (Category.comp_id (pullback.fst (fieldMorphism B S hS F p) φ)).symm)
  exact (Q.presheaf.arrow_mk_iso_iff harrow).mpr hQpre

/-! ### The relation fibre above a point with a finite chart fibre -/

/-- Let `φ : h_U ⟶ F` be an étale chart of an algebraic space `F` over `S` and let `x` be a point
of `|F|` represented by a monomorphism out of the spectrum of a field whose fibre on `|U|` is
finite. Then the fibre of `|R| → |F|` above `x`, where `R = h_U ×_F h_U`, is finite. -/
theorem finite_relationFibre_of_finite_chartFibre (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) {x : points B S hS F} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ F} (hφ : IsEtale B S hS φ)
    (hmono : HasMonomorphicFieldRepresentative B S hS F x)
    (hchart : (chartFibre B S hS F φ x).Finite) :
    (relationFibre B S hS F φ x).Finite := by
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let D : PointsFibresDiagram B S hS :=
    { W := pullback φ φ
      Z := yoneda.obj U
      X := yoneda.obj U
      Y := F
      W_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS φ φ hUalg hUalg hF
      Z_isAlgebraicSpace := hUalg
      X_isAlgebraicSpace := hUalg
      Y_isAlgebraicSpace := hF
      q := pullback.snd φ φ
      p := pullback.fst φ φ
      f := φ
      g := φ
      isPullback := IsPullback.of_hasPullback φ φ }
  have hqf : ∀ b : points B S hS (yoneda.obj U), IsQuasiFiniteAt B S hS φ b := fun b ↦
    isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hUalg
      (isLocallyQuasiFinite_of_isEtale B S hS hF hφ) b
  have hsub : relationFibre B S hS F φ x ⊆
      ⋃ a ∈ chartFibre B S hS F φ x, ⋃ b ∈ chartFibre B S hS F φ x,
        {r : points B S hS (pullback φ φ) |
          pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r = a ∧
          pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r = b} := by
    intro r hr
    have ha : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r) = x := by
      rw [← pointsMap_comp_apply]
      exact hr
    have hb : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r) = x := by
      rw [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply]
      exact ha
    exact Set.mem_biUnion ha (Set.mem_biUnion hb ⟨rfl, rfl⟩)
  refine Set.Finite.subset (Set.Finite.biUnion hchart fun a ha ↦
    Set.Finite.biUnion hchart fun b hb ↦ ?_) hsub
  have ha' : pointsMap B S hS (yoneda.obj U) φ a = x := ha
  have hb' : pointsMap B S hS (yoneda.obj U) φ b = x := hb
  have hcomm : pointsMap B S hS D.X D.f a = pointsMap B S hS D.Z D.g b := by
    show pointsMap B S hS (yoneda.obj U) φ a = pointsMap B S hS (yoneda.obj U) φ b
    rw [ha', hb']
  have hy : HasMonomorphicFieldRepresentative B S hS D.Y
      (pointsMap B S hS D.X D.f a) := by
    show HasMonomorphicFieldRepresentative B S hS F (pointsMap B S hS (yoneda.obj U) φ a)
    rwa [ha']
  exact finite_fibrePoints_of_mono_of_isQuasiFiniteAt D a b hcomm hy (hqf b)

/-! ### Stacks 040U, part (2) implies part (1) -/

/-- A monomorphic field-valued representative of `x` whose base change along an étale chart
`φ : h_U ⟶ F` is a finite morphism of algebraic spaces makes both the fibre of `|U| → |F|` and
the fibre of `|R| → |F|` above `x` finite, where `R = h_U ×_F h_U`. -/
theorem finite_chartFibre_and_relationFibre_of_mono_isFinite
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ F}
    (hφ : IsEtale B S hS φ) (p : FieldValuedPoint B S hS F) (hpx : p.class B S hS F = x)
    (hmono : Mono (fieldMorphism B S hS F p))
    (hIsFin : IsFinite B S hS (pullback.fst (fieldMorphism B S hS F p) φ)) :
    (chartFibre B S hS F φ x).Finite ∧ (relationFibre B S hS F φ x).Finite := by
  have hffin : Finite (points B S hS (fieldFibre B S hS φ p)) :=
    finite_points_fieldFibre_of_isFinite B S hS p φ hIsFin
  have hchart : (chartFibre B S hS F φ x).Finite := by
    rw [← hpx]
    exact finite_setFibre_of_finite_fieldFibre B S hS (isAlgebraicSpace_yoneda B S hS U) hF
      φ p Set.finite_univ
  exact ⟨hchart,
    finite_relationFibre_of_finite_chartFibre B S hS F hF hφ ⟨p, hpx, hmono⟩ hchart⟩

/-- Let `F` be an algebraic space over a scheme `S`, let `x` be a point of `|F|` and let
`φ : h_U ⟶ F` be étale. Suppose some field-valued point of `F` in the class of `x` presents it by
a monomorphism `Spec(k) ⟶ F` for which `Spec(k) ×_F U` is nonempty and finite over `Spec(k)`.
Then `x` lies in the image of `|U| → |F|` and the fibres of `|U| → |F|` and of `|R| → |F|` above
`x`, where `R = h_U ×_F h_U`, are both finite. -/
@[stacks 040U "part (2) implies part (1)"]
theorem finiteFibres_of_mono_isFinite_fieldFibre (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) {x : points B S hS F} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ F} (hφ : IsEtale B S hS φ)
    (h : ∃ p : FieldValuedPoint B S hS F, p.class B S hS F = x ∧
      Mono (fieldMorphism B S hS F p) ∧
      IsFinite B S hS (pullback.fst (fieldMorphism B S hS F p) φ) ∧
      Nonempty (points B S hS (pullback (fieldMorphism B S hS F p) φ))) :
    (∃ a : points B S hS (yoneda.obj U), pointsMap B S hS (yoneda.obj U) φ a = x) ∧
      (chartFibre B S hS F φ x).Finite ∧ (relationFibre B S hS F φ x).Finite := by
  obtain ⟨p, hpx, hmono, hIsFin, hne⟩ := h
  refine ⟨?_, finite_chartFibre_and_relationFibre_of_mono_isFinite B S hS F hF hφ p hpx
    hmono hIsFin⟩
  have hneF : Nonempty (points B S hS (fieldFibre B S hS φ p)) :=
    hne.map (pointsMap B S hS _ (pullbackSymmetry (fieldMorphism B S hS F p) φ).hom)
  obtain ⟨a, ha⟩ := (nonempty_points_fieldFibre_iff B S hS φ p).mp hneF
  exact ⟨a, ha.trans hpx⟩

/-! ### Stacks 040U, part (1) implies part (2) -/

/-- A point `x` of `|F|` lying in the image of `|U| → |F|` whose chart and relation fibres above
it are finite is presented by a monomorphism `Spec(k) ⟶ F` for which `Spec(k) ×_F U` is nonempty
and finite over `Spec(k)`, finiteness being the presheaf-relative form. -/
@[stacks 040U "part (1) implies part (2)"]
theorem exists_mono_isFinite_fieldFibre_of_finiteFibres
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ F}
    (hφ : IsEtale B S hS φ)
    (h : (∃ a : points B S hS (yoneda.obj U), pointsMap B S hS (yoneda.obj U) φ a = x) ∧
      (chartFibre B S hS F φ x).Finite ∧ (relationFibre B S hS F φ x).Finite) :
    ∃ p : FieldValuedPoint B S hS F, p.class B S hS F = x ∧
      Mono (fieldMorphism B S hS F p) ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.fst (fieldMorphism B S hS F p) φ) ∧
      Nonempty (points B S hS (pullback (fieldMorphism B S hS F p) φ)) := by
  obtain ⟨⟨a, ha⟩, hchart, hrel⟩ := h
  have h1 : HasFiniteRelationFiberAt B S hS F x := by
    refine ⟨U, φ, a, a, hφ, ha, ha, hrel.subset ?_⟩
    rintro r ⟨hra, -⟩
    show pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) r = x
    rw [pointsMap_comp, Function.comp_apply, hra, ha]
  obtain ⟨p, hpx, hmono⟩ :=
    HasFiniteRelationFiberAtEveryEtaleChart.hasMonomorphicFieldRepresentative B S hS F hF
      (h1.hasFiniteRelationFiberAtEveryEtaleChart B S hS F hF)
  have heq : setFibre B S hS φ p = chartFibre B S hS F φ x :=
    Set.ext fun b ↦ ⟨fun hb ↦ hb.trans hpx, fun hb ↦ hb.trans hpx.symm⟩
  have hsf : (setFibre B S hS φ p).Finite := heq ▸ hchart
  have hffin : Finite (points B S hS (fieldFibre B S hS φ p)) :=
    Set.finite_univ_iff.mp
      (finite_univ_points_fieldFibre_of_finite_setFibre B S hS φ p hmono hsf)
  refine ⟨p, hpx, hmono,
    presheaf_isFinite_pullback_fst_fieldMorphism_of_finite_points B S hS p hφ hffin, ?_⟩
  obtain ⟨w⟩ := (nonempty_points_fieldFibre_iff B S hS φ p).mpr ⟨a, ha.trans hpx.symm⟩
  exact ⟨pointsMap B S hS _ (pullbackSymmetry φ (fieldMorphism B S hS F p)).hom w⟩

/-- For an étale chart `φ : h_U ⟶ F` of an algebraic space `F` over `S` and a point `x` of `|F|`,
the point lies in the image of `|U| → |F|` with finite chart and relation fibres exactly when
some monomorphism `Spec(k) ⟶ F` in the class of `x` has `Spec(k) ×_F U` nonempty and finite over
`Spec(k)`, finiteness being the presheaf-relative form. -/
theorem finiteFibres_iff_exists_mono_isFinite_fieldFibre
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ F}
    (hφ : IsEtale B S hS φ) :
    ((∃ a : points B S hS (yoneda.obj U), pointsMap B S hS (yoneda.obj U) φ a = x) ∧
        (chartFibre B S hS F φ x).Finite ∧ (relationFibre B S hS F φ x).Finite) ↔
      ∃ p : FieldValuedPoint B S hS F, p.class B S hS F = x ∧
        Mono (fieldMorphism B S hS F p) ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.fst (fieldMorphism B S hS F p) φ) ∧
        Nonempty (points B S hS (pullback (fieldMorphism B S hS F p) φ)) := by
  refine ⟨exists_mono_isFinite_fieldFibre_of_finiteFibres B S hS F hF hφ, ?_⟩
  rintro ⟨p, hpx, hmono, hpre, hnonempty⟩
  exact finiteFibres_of_mono_isFinite_fieldFibre B S hS F hF hφ
    ⟨p, hpx, hmono, isFinite_of_presheaf_isFinite B S hS _ hpre, hnonempty⟩

/-! ### Two special cases of the implication of Stacks 03JU used above -/

/-- Condition (2) of Stacks 03JU implies condition (4) at every point of a decent algebraic space
over `S`. -/
theorem hasMonomorphicFieldRepresentative_of_everyEtaleChart_of_isDecentSpace
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsDecentSpace B S hS F)
    (x : points B S hS F) :
    HasFiniteRelationFiberAtEveryEtaleChart B S hS F x →
      HasMonomorphicFieldRepresentative B S hS F x :=
  fun _ ↦ hF.hasMonomorphicFieldRepresentative B S hS F x

/-- Condition (2) of Stacks 03JU implies condition (4) at every point of a presheaf represented by
an object of the big fppf site. -/
theorem hasMonomorphicFieldRepresentative_of_everyEtaleChart_yoneda
    (T : BigFppfOver B S hS) (x : points B S hS (yoneda.obj T)) :
    HasFiniteRelationFiberAtEveryEtaleChart B S hS (yoneda.obj T) x →
      HasMonomorphicFieldRepresentative B S hS (yoneda.obj T) x :=
  hasMonomorphicFieldRepresentative_of_everyEtaleChart_of_isDecentSpace B S hS
    (yoneda.obj T) (isDecentSpace_yoneda B S hS T) x

end AlgebraicGeometry.Space

end
